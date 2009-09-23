(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2009                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Sig

module type S = sig
  type t

  val empty : unit -> t
  val add : Literal.t -> t -> t
  val assume : Literal.t -> Explanation.t -> t -> t
  val query : Literal.t -> t -> bool
  val class_of : t -> Term.t -> Term.t list
  val explain : Literal.t -> t -> Explanation.t
end

module Make (X : Sig.X) = struct    

  module Ex = Explanation
  module Use = Use.Make(X)
  module Uf = Uf.Make(X)
  module SetF = Formula.Set
  module T = Term
  module A = Literal
  module SetT = Term.Set
  module SetA = A.Set
  module SAeq = A.SetEq
  module S = Symbols

  module SetX = Set.Make(struct type t = X.r let compare = X.compare end)
    
  type t = { 
    use : Use.t;  
    uf : Uf.t ;
    relation : X.R.t;
  }

  module Print = struct

    let lrepr fmt = List.iter (fprintf fmt "%a " X.print)

    let congruent t1 t2 flg = 
      fprintf fmt "@{<C.Bold>[cc]@} cong %a=%a ? [%s]@." 
	T.print t1 T.print t2 flg

    let add_to_use t = fprintf fmt "@{<C.Bold>[cc]@} add_to_use: %a@." T.print t
	
    let leaves t lvs = 
      fprintf fmt "@{<C.Bold>[cc]@} leaves of %a@.@." T.print t; lrepr fmt lvs
  end

  let compat_leaves env lt1 lt2 = 
    List.fold_left2
      (fun dep x y -> Ex.union (Uf.explain env.uf x y) dep) Ex.empty lt1 lt2

  let congruent env u1 u2 = 
    try
      let {T.f=f1;xs=xs1;ty=ty1} = T.view u1 in
      let {T.f=f2;xs=xs2;ty=ty2} = T.view u2 in
      if S.equal f1 f2 && Ty.equal ty1 ty2 then
	compat_leaves env xs1 xs2
      else raise Exception.NotCongruent
    with 
      | Exception.NotCongruent as e ->
	  if debug_cc then Print.congruent u1 u2 "No-NC";
	  raise e
      | e -> 
	  if debug_cc then Print.congruent u1 u2 "No-OE";
	  (* raise e *)
	  raise Exception.NotCongruent
	      
  let concat_leaves uf l = 
    let one = X.make (Term.make (S.name "@bottom") [] Ty.Tint) in 
    let rec concat_rec acc t = 
      match  X.leaves (Uf.find uf t) , acc with
	  [] , _ -> one::acc
	| res, [] -> res
	| res , _ -> List.rev_append res acc
    in
    match List.fold_left concat_rec [] l with
	[] -> [one]
      | res -> res

  let is_constant t = match (T.view t).T.xs with [] -> true | _ -> false
    
  let uninterpreted rt = match X.leaves rt with
    | []  -> false     (* true aurait ete plus general *)
    | [y] -> rt = y
    | _   -> false

  let rec close_up t1 t2 dep env =
    if debug_cc then 
      printf "@{<C.Bold>[cc]@} close_up: %a=%a@." T.print t1 T.print t2;
    (* nothing to do if the terms are known to be equal *)
    if Uf.equal env.uf t1 t2 then env
    else

      (* looking for representants of t1 and t2 *)
      let r1 = Uf.find env.uf t1 in
      let r2 = Uf.find env.uf t2 in 
      
      (* we solve [t1]=[t2] which yields :
	 - a new union-find uf 
	 - a list of substitutions [ p |-> v ] with a list of touched 
	 semantical values for each substitution *)
      
      if debug_cc then 
	printf "[cc] union %a = %a@." T.print t1 T.print t2;
      let uf, res = Uf.union env.uf r1 r2 dep in
      List.fold_left 
	(fun env (p,touched,v) ->
	   
	   (* we look for use(p) *)
      	   let gm_p_t, gm_p_a = Use.find p env.use in

	   (* we compute terms and atoms to consider for congruence *)
	   let st_others, sa_others = Use.congr_close_up env.use p touched in

	   (* we update use *)
	   let nuse = Use.up_close_up env.use p v in
	  
	   (* we print updates in Gamma and Ac-Gamma *)
	   if debug_use then Use.print nuse;
 
	   (* we check the congruence of the terms. 
	      It's only done on uninterpreted functions symbols *)
	   
	   let u_gm_p_t = 
	     T.Set.filter (fun t ->uninterpreted(Uf.find env.uf t))gm_p_t in
	   let u_st_others = 
	     T.Set.filter (fun t ->uninterpreted(Uf.find env.uf t))st_others in

	   let env = replay_terms u_gm_p_t u_st_others {env with use=nuse} in

	   (* we check the congruence of the atoms *)
	   replay_atom (SetA.union gm_p_a sa_others) env

	) {env with uf=uf}  res


  and replay_terms gm_p_t st_others env = 
    SetT.fold 
      (fun x env -> 
	 SetT.fold 
	   (fun y env -> 
	      try close_up x y (congruent env x y) env
	      with Exception.NotCongruent -> env
	   )st_others env
      )gm_p_t env


  and replay_atom sa env = 
    let rel , nsa  = 
      X.R.assume env.relation sa (Uf.find env.uf) (Uf.class_of env.uf) in
    SAeq.fold 
      (fun (a,t1,t2) env -> 
	 let r1 = Uf.find env.uf t1 in
	 let r2 = Uf.find env.uf t2 in
	 let st_r1 , sa_r1 = Use.find r1 env.use in
	 let st_r2 , sa_r2 = Use.find r2 env.use in
	 let sa_r1' , sa_r2' = SetA.remove a sa_r1 , SetA.remove a sa_r2 in
	 let use =  Use.add r1 (st_r1,sa_r1') env.use in
	 let use =  Use.add r2 (st_r2,sa_r2') use in	     
	 let env = close_up t1 t2 Ex.everything { env with use = use} in
	 env
      ) nsa { env with relation = rel }
  

  let congruents e t s acc = 
    SetT.fold 
      (fun t2 acc ->
	 (* t and t2 are syntactically equal *)
	 if T.equal t t2 then acc
	 else 
	   try 
	     let acc = (t,t2,congruent e t t2)::acc in
	     if debug_cc then Print.congruent t t2 "Yes"; acc
	   with Exception.NotCongruent -> 
	     if debug_cc then Print.congruent t t2 "No-NC"; acc
      ) s acc
	   
  (* add a new term in env *)   	

  let rec add_term (env,ct) t = 
    if debug_cc then Print.add_to_use t;
    (* nothing to do if the term already exists *)
    if Uf.mem env.uf t then (env,ct)
    else
      (* we add t's arguments in env *)
      let {T.f = f; xs = xs} = T.view t in
      let env , ct = List.fold_left add_term (env,ct) xs in
      (* we update uf and use *)
      let nuf  = Uf.add env.uf t in
      let rt   = Uf.find nuf t in
      let nuse = Use.up_add env.use t rt (concat_leaves nuf xs) in
      
      (* print updates in Gamma *)
      if debug_use then Use.print nuse;

      (* we compute terms to consider for congruence *)
      (* we do this only for non-atomic terms with uninterpreted head-symbol *)
      if not (is_constant t) && uninterpreted rt then
	let lvs = concat_leaves nuf xs in
	let st_uset = Use.congr_add nuse lvs in

	(* we check the congruence of each term *)
	let env = {env with uf = nuf; use = nuse} in 
	(env,congruents env t st_uset ct)
      else ({env with uf = nuf; use = nuse}, ct)
	
  let add a env =
    let st = A.terms_of a in
    let env = 
      SetT.fold
	(fun t env -> 
	   let env , ct = add_term (env,[]) t in
	   List.fold_left
	     (fun e (x,y,dep) -> close_up x y dep e) env ct) st env
    in 
    match A.view a with
	A.Eq _ | A.Neq _ -> env
      | _ ->
	  let lvs = concat_leaves env.uf (Term.Set.elements st) in
	  List.fold_left
	    (fun env rx ->
	       let st_uset , sa_uset = Use.find rx env.use in
	       {env with use=Use.add rx (st_uset,SetA.add a sa_uset) env.use}
	    ) env lvs

  let assume a dep env = 
    let env  = add a env in
    match A.view a with
	A.Eq(t1,t2) -> close_up t1 t2 dep env
      | A.Neq(t1,t2)-> 
	  replay_atom (SetA.singleton a) 
	    {env with uf = Uf.distinct env.uf t1 t2 dep}
      | _ -> replay_atom (SetA.singleton a) env

  let class_of env t = Uf.class_of env.uf t

  let explain a env = try
    (match A.view a with
      | A.Eq(x,y) -> Uf.explain env.uf x y
      | A.Neq(x,y) -> Uf.neq_explain env.uf x y
      | _ -> Ex.everything)
  with Exception.NotCongruent -> assert false
	      
  let query a env = 
    if debug_use then Use.print env.use;
    match A.view a with
	A.Eq(t1,t2)  -> Uf.equal env.uf t1 t2
      | A.Neq(t1,t2) -> Uf.are_distinct env.uf t1 t2
      | _ -> X.R.query (A.neg a) (Uf.find env.uf) (class_of env) env.relation
    
  let empty _ = 
    let env = { 
      use = Use.empty ; 
      uf = Uf.empty ; 
      relation = X.R.empty ()}
    in
    assume (A.make (A.Neq(T.vrai,T.faux))) Ex.empty env 

end
