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
open Exception

module type S = sig
  type t

  module R : Sig.X

  val empty :  t
  val add : t -> Term.t -> t
  val mem : t -> Term.t -> bool
  val find : t -> Term.t -> R.r
  val union : 
    t -> R.r -> R.r -> Explanation.t ->
    t * (R.r * ((R.r * R.r) list) * R.r) list

  val distinct : t -> Term.t -> Term.t -> Explanation.t -> t

  val equal : t -> Term.t -> Term.t -> bool
  val are_distinct : t -> Term.t -> Term.t -> bool
  val class_of : t -> Term.t -> Term.t list

  val explain : t -> Term.t -> Term.t -> Explanation.t
  val neq_explain : t -> Term.t -> Term.t -> Explanation.t

end

module Make ( R : Sig.X ) = struct

  module L  = List
  module Ex = Explanation
  module R = R
  module S = Symbols
  module T = Term
  module F = Formula
  module MapT = Term.Map
  module SetT = Term.Set
  module SetF = Formula.Set

  module IM = struct
    include Set.Make(
      struct 
	type t = R.r * R.r
	let compare (a,x) (b,y) =
	  let c = R.compare a b in if c <> 0 then c else R.compare x y
      end)
    let print_elt fmt (v,g) = 
      fprintf fmt "%a | %a" R.print v R.print g
    let print fmt t = 
      iter (fprintf fmt "\n\t%a" print_elt) t
  end
  
  type repr = {re:R.r ; im:IM.t ; ex : Ex.t}

  module MapR = Map.Make(struct type t = R.r let compare = R.compare end)

  module SetR = Set.Make(struct type t = R.r let compare = R.compare end)

  type t = { 
    make : R.r MapT.t; (* term -> [t] *)
    repr : repr MapR.t; (* representative table *)
    classes : SetT.t MapR.t;  (* r -> class (of terms) *)
    gamma : SetR.t MapR.t; 
    (* associates each value r with the set of semantical values whose
       representatives contains r *)
    neqs: Ex.t MapR.t MapR.t; (* the disequations map *)
  }
      
  let empty = { 
    make  = MapT.empty; 
    repr = MapR.empty;
    classes = MapR.empty; 
    gamma = MapR.empty;
    neqs = MapR.empty;
  }

  module Print = struct

    let rs_print fmt = SetR.iter (fprintf fmt "%a " R.print)
    let rm_print fmt = MapR.iter (fun k _ -> fprintf fmt "%a " R.print k)

    let t_print fmt = SetT.iter (fprintf fmt "%a " T.print)
      
    let pmake fmt m = 
      fprintf fmt "[.] map:\n";
      MapT.iter (fun t r -> fprintf fmt "%a -> %a\n" T.print t R.print r) m
	
    let prepr fmt m = 
      fprintf fmt "Representatives map:\n";
      MapR.iter 
	(fun r rr -> 
	   fprintf fmt "%a -> %a%a\n" R.print r R.print rr.re 
	     IM.print rr.im)m
	
    let pclasses fmt m = 
      fprintf fmt "Classes map:\n";
      MapR.iter 
	(fun k s -> fprintf fmt "%a -> %a\n" R.print k Term.print_list 
	   (SetT.elements s)) m

    let pgamma fmt m = 
      fprintf fmt "Gamma map:\n";
      MapR.iter (fun k s -> fprintf fmt "%a -> %a\n" R.print k rs_print s) m 
		
    let pneqs fmt m = 
      fprintf fmt "Disequations map:\n";
      MapR.iter (fun k s -> fprintf fmt "%a -> %a\n" R.print k rm_print s) m

    let all env = 
      printf "---------- UF environment --------@.";
      printf "%a\n%a\n%a\n%a\n" 
	pmake env.make prepr env.repr pneqs env.neqs pclasses env.classes;
      printf "---------- FIN UF environment --------@."

  end

  let mem env t = MapT.mem t env.make
      
  let find env t = 
    try MapR.find (MapT.find t env.make) env.repr
    with Not_found -> {re=R.make t ; im=IM.empty ; ex=Ex.empty}

  let findr env r = 
    try MapR.find r env.repr
    with Not_found -> {re=r ; im=IM.empty ; ex=Ex.empty}
    

  (*** AC functions ***)
  module AC = struct
    let fp = Format.fprintf

    (* tentative *)
    let re_embed c2 c = 
      match R.ac_extract c2 , R.ac_extract c with
	| Some (hs2, _), Some (hs, _) when Hstring.equal hs2 hs -> c2
	| (Some _ | None), Some(hs, _) -> R.ac_embed (hs, [c2])
	| _ , None -> assert false

    let open_ac v =
      match R.ac_extract v with
	  Some(hs,xs) -> hs, xs
	| _ -> assert false

    let is_trivial r (s,g) =
      let hs,xs = open_ac g in
      R.compare s (R.ac_embed (hs, r::xs)) = 0
	
    let orient p v =
      let p',v' =
	let c = R.compare p v in
	if c = 0 then assert false
	else if c > 0 then p,v else v,p
      in
      if debug_ac then
	fp fmt "[AC] orient\n # %a -> %a donne \n # %a = %a@."
	  R.print p R.print v R.print p' R.print v';
      p',v'
	
    let ac_solve (hs,xs) v = 
      let rec split acc dn td = match td with
	| []   -> acc
	| e::r -> 
	    let sb = e,(v, R.ac_embed (hs,dn@r)) in 
	    split (sb::acc) (e::dn) r 
      in 
      match xs with
	|[]|[_] -> assert false
	| _     -> split [] [] xs
	    
  (* p is known to be greater than v *)
  let solve p v = match R.ac_extract p with
    | Some (hs,xs) -> ac_solve (hs,xs) v
    | None         -> []
    
  let remove_intersection l1 l2 = 
    let sort l = L.fast_sort R.compare l in
    let rec rm_inter (x,y) = function
	[]   , []   -> x    , y
      | ls   , []   -> ls@x , y
      | []   , ls   -> x    , ls@y  
      | a::r , b::s -> 
 	  let c = R.compare a b in
	  if c = 0 then rm_inter (x,y) (r,s)
	  else if c > 0 then rm_inter (x,b::y) (a::r,s)
	  else rm_inter (a::x,y) (r,b::s)
    in rm_inter ([],[]) (sort l1, sort l2)
	 
  let cross_terms (hs,xs) v2 = match xs with
    | [] -> v2
    | _  -> 
	let new_xs = match R.ac_extract v2 with
	  | Some(h,ls) when Hstring.equal h hs -> ls @ xs
	  | _ -> v2 :: xs
	in R.ac_embed (hs,new_xs)
	     
  let mk_cpair pc_acc (sb1,cd1) im_ls = 
    let h1,l1 = open_ac cd1 in
    IM.fold 
      (fun (sb2, cd2) acc ->
	 let h2,l2 = open_ac cd2 in
	 if Hstring.equal h1 h2 then
	   let l1,l2 = remove_intersection l1 l2 in
	   (cross_terms (h1,l1) sb2 , cross_terms (h2,l2) sb1) :: acc
	 else acc
      )im_ls pc_acc

  let mk_pic acc_pic re im = 
    IM.fold
      (fun (sb,cd) acc -> 
	 let h,l = open_ac cd in (sb,cross_terms (h,l) re)::acc
      ) im acc_pic
      
    (********************************************************)
	
    let remove_once a l = 
      let eq a b = R.compare a b = 0 in
      let rec f acc = function
	  [] -> raise Not_found
	| p::r -> if eq p a then (L.rev acc)@r else f (p::acc) r
      in f [] l
	   
    let remove_sl sub_l l = 
      L.fold_left (fun acc a -> remove_once a acc) l sub_l
	
    let flat hs2 e = match R.ac_extract e with
      | Some (hs,xs) when Hstring.equal hs hs2 -> xs
      | _ -> [e]
	  
    let rev_sort l = L.rev (L.fast_sort R.compare l)
      
    let rec apply_img hs xs = function 
	[]          -> false, xs
      | (s,g)::rest -> 
	  let sb_hs,sb_xs = open_ac g in
	  try 
	    if Hstring.equal hs sb_hs then
	      true, (flat hs s) @ (remove_sl sb_xs xs)
	    else raise Not_found
	  with Not_found -> apply_img hs xs rest
	    
	    
    let ac_subst env hs xs = 
      let rec f xs xs_acc = 
	match xs with 
	  | []   -> xs_acc
	  | p::r -> 
	      let im_p = IM.elements ((findr env p).im) in
	      let touched,xs = apply_img hs r im_p in
	      if touched then f (rev_sort (xs@xs_acc)) []
	      else f r (p::xs_acc)
      in 
      f (rev_sort xs) []
	
    (********************************************************)
	
	
    let rec ac_canon env rx = 
      match R.is_empty rx , R.ac_extract rx with
	| true , None    -> rx            (* a real leaf  *)
	| true , Some ac -> can_ac env ac (* an AC leaf   *)
	| false, None    -> can_x env rx  (* Not a leaf   *)
	| false, Some _  -> assert false  (* not possible *)
	    
    and can_ac env (hs,xs) = 
      let xs = can_args env hs xs in
      match ac_subst env hs xs with
	  []  -> assert false
	| [a] -> a
	| new_xs  -> R.ac_embed (hs,new_xs) 
	      
    and can_args env hs xs = 
      L.fold_left
	(fun acc r ->
	   let rr = ac_canon env r in
	   match R.ac_extract rr with
	     | Some(h,l) when Hstring.equal hs h -> l@acc
	     | _ -> rr :: acc
	)[] xs 
	
    and can_x env rx =
      let ls = 
	L.fold_left
	  (fun acc p -> 
	     let v = ac_canon env p in 
	     if R.compare v p = 0 then acc else (p,v)::acc
	  )[] (R.leaves rx)
      in 
      L.fold_left (fun acc (p,v) -> R.subst p v acc) rx ls
	
  end
    
    
    
  module Env = struct
    
    let add_to_classes t r classes =  
      MapR.add r 
	(SetT.add t (try MapR.find r classes with Not_found -> SetT.empty))
	classes

    let update_classes c nc classes = 
      let s1 = try MapR.find c classes with Not_found -> SetT.empty in
      let s2 = try MapR.find nc classes with Not_found -> SetT.empty in
      MapR.add nc (SetT.union s1 s2) classes

    let add_to_gamma r c gamma = 
      L.fold_left
	(fun gamma x -> 
	   let s = try MapR.find x gamma with Not_found -> SetR.empty in
	   MapR.add x (SetR.add r s) gamma) gamma (R.leaves c)
	
    let merge r1 m1 r2 m2 dep neqs = 
      let m , neqs = 
	MapR.fold 
	  (fun k ex1 (m,neqs) -> 
	     if MapR.mem k m2 then
	       m , MapR.add k (MapR.remove r1 (MapR.find k neqs)) neqs
	     else
	       let ex = Ex.union ex1 dep in
	       let mk = MapR.add r2 ex (MapR.remove r1 (MapR.find k neqs)) in
	       MapR.add k ex m , MapR.add k mk neqs
	  )
	  m1 (m2,neqs)
      in
      MapR.add r2 m neqs


    let update_neqs r1 r2 dep env = 
      let neqs, m1 = 
	try env.neqs, MapR.find r1 env.neqs 
	with Not_found -> MapR.add r1 MapR.empty env.neqs, MapR.empty in
      let neqs, m2 = 
	try neqs, MapR.find r2 neqs 
	with Not_found -> MapR.add r2 MapR.empty neqs, MapR.empty in
      if MapR.mem r2 m1 or MapR.mem r1 m2 then raise Inconsistent;
      merge r1 m1 r2 m2 dep neqs

    let add_repr r new_rr repr = 
      try
	let rr = MapR.find r repr in
	let im = IM.union new_rr.im rr.im in
	let c = R.compare rr.re new_rr.re in
	if c > 0 then MapR.add r {new_rr with im=im} repr
	else MapR.add r {rr with im=im} repr
      with Not_found -> MapR.add r new_rr repr
 

    let canon env init = 
      let lvs = R.leaves init.re in 
      L.fold_left
	(fun q x -> 
	   try
	     let rx = MapR.find x env.repr in
	     {q with re = R.subst x rx.re q.re; ex = Ex.union q.ex rx.ex}
	   with Not_found -> q
	)init lvs

    let ac_init env r =  
      try (* r is already initialized *)
	env, (MapR.find r env.repr).re  
      with Not_found ->
	let ac_r = AC.ac_canon env r in
	let ac_rep = {re=ac_r ; im=IM.empty; ex=Ex.empty} in
	let env = 
	  { env with 
              repr = add_repr r ac_rep env.repr ;
	      gamma = add_to_gamma r ac_rep.re env.gamma;
	      neqs = 
	      if MapR.mem ac_rep.re env.neqs then env.neqs 
	      else MapR.add ac_rep.re MapR.empty env.neqs}
	in env,ac_rep.re

	

    (* canon d'abord, ac_canon ensuite car
       si t = f(c,gamma+x) et que x vaut 0, cela ne va pas
       etre pris en compte dans ac_canon car applique en premier *)
    let init env t r = 
      let init = {re=r ; im=IM.empty; ex=Ex.empty} in
      let rep = canon env init in
      let rep = {rep with re=AC.ac_canon env rep.re} in

      { make = MapT.add t r env.make; 
	repr = add_repr r rep env.repr ;
	
	classes = add_to_classes t rep.re env.classes;
	gamma = add_to_gamma r rep.re env.gamma;
	neqs = 
	  if MapR.mem rep.re env.neqs then env.neqs 
	  else MapR.add rep.re MapR.empty env.neqs
      }

    (* Guarded rule *)
    let guarded (env,cp) (r,csb) =
      if debug_uf then printf "[AC] AC-subst %a |-> %a@." 
	R.print r IM.print_elt csb;
      let rr = findr env r  in
      if IM.mem csb rr.im then (env,cp)
      else
	let cp = AC.mk_cpair cp csb rr.im in
	(* simplifs ici, + infos a mettres dans gamma *)
	let nrr = {rr with im = IM.add csb rr.im } in
	{ env with repr=MapR.add r nrr env.repr} , cp
	  
    let changed u v = R.compare u v <> 0
      
    let update_im p v im = 
      IM.fold
	(fun (s,c) (st,touched) -> 
	   let s2 = R.subst p v s in
	   let c2 = R.subst p v c in
	   let c2 = AC.re_embed c2 c in
	   if changed s s2 || changed c c2 then st , IM.add (s2,c2) touched
	   else IM.add (s2,c2) st , touched
	) im (IM.empty,IM.empty)
	
    let reorient mk lre nre = 
      let res = R.is_empty mk && not (R.is_empty lre) && R.is_empty nre in
      if debug_ac && res then
	fprintf fmt "[AC] REORIENT %a -> %a@." R.print mk R.print nre;
      res

    let update env p v dep = 
      MapR.fold 
	(fun r rr (env,touched,repl,ac_repl) ->
	   let nex = Ex.union rr.ex dep in
	   let nre = R.subst p v rr.re in
	   let touched_re = changed nre rr.re in
	   let nim, touched_im = update_im p v rr.im in
	   let nrr  = {re=nre; im=nim; ex=nex} in
	   let reorient = reorient r rr.re nre in
	   match touched_re, reorient, IM.is_empty nim with
	     | true , true , _ -> 
		 let mk_r = {re=r;im=IM.empty;ex=Ex.empty} in
		 let repr = MapR.add r mk_r env.repr in
		 let env = {env with repr=repr }in 
		 env, touched, AC.mk_pic ((r,nre)::repl) nre nim, ac_repl

	     | true , false, false -> 
		 let nrr  = {nrr with im= IM.empty} in
		 let env = 
		   {env with 
		      repr = MapR.add r nrr env.repr;
		      classes = update_classes rr.re nre env.classes;
		      gamma = add_to_gamma r nre env.gamma ;
		      neqs = update_neqs rr.re nre dep env
		   } in 
		 let repl = AC.mk_pic ((rr.re,nre)::repl) nre nim in
		 env,(r,nre)::touched,repl, ac_repl
		   
	     | true , false, true -> 
		 let ac_repl = AC.mk_pic ac_repl nre touched_im in
		 let env = 
		   {env with 
		      repr = MapR.add r nrr env.repr;
		      classes = update_classes rr.re nre env.classes;
		      gamma = add_to_gamma r nre env.gamma ;
		      neqs = update_neqs rr.re nre dep env 
		   } in 
		 env, (r,nre)::touched,repl,ac_repl

	     | false, _ , _ ->
		 let ac_repl = AC.mk_pic ac_repl nre touched_im in
		 let env = 
		   {env with 
		      repr = MapR.add r nrr env.repr;
		      classes = update_classes rr.re nre env.classes;
		      gamma = add_to_gamma r nre env.gamma ;
		      neqs = update_neqs rr.re nre dep env
		   } in 
		 env,touched,repl, ac_repl

	) env.repr (env,[],[],[]) 
	
  end
    
  let add env t = 
    if MapT.mem t env.make then env else Env.init env t (R.make t)
    
  let rec union env r1 r2 dep = 
    (* the equation is trivial *)
    if R.compare r1 r2 = 0 then env , []
    else
      try
	if debug_uf then printf "[uf] union %a = %a@." R.print r1 R.print r2;

	(* if r1 is known to be different from r2, there is inconsistency *)
	let nq_r1 = try MapR.find r1 env.neqs with Not_found -> MapR.empty in
	let nq_r2 = try MapR.find r2 env.neqs with Not_found -> MapR.empty in
	if MapR.mem r2 nq_r1 then raise Inconsistent;
	if MapR.mem r1 nq_r2 then raise Inconsistent;
	
	(* applying R.solve on r1 = r2 *) 
	let xsubsts = R.solve r1 r2 in

	(* applying xsusbts in Delta and computing touched representatives *)
	let env,cp,res = L.fold_left (apply_pivot dep) (env,[],[]) xsubsts in
	if debug_uf then Print.all env;
	
	union_cp dep (env,res) cp 

      with Unsolvable -> raise Inconsistent

  and apply_pivot dep (env, cp, res) (p,v) =
    (* orient the substitution *)
    let p , v = AC.orient p v in 
    
    (* apply p|-> v on Delta *)
    if debug_uf then printf "[uf] X-subst %a |-> %a@." R.print p R.print v;
    let env2,touched,repl,ac_repl = Env.update env p v dep in

    let env3,res2 = union_repl dep (env2,res) repl in   

    (* replay p = v in AC *)

    let eqs = AC.solve p v in
    let env4,cp = L.fold_left Env.guarded (env3,cp) eqs in

    let env5,cp = 
      L.fold_left
	(fun (envi,cps) (x,y) ->
	   if R.compare x y = 0 then (envi,cps) 
	   else 
	     begin
	       if debug_ac then 
		 fprintf fmt "[AC] replay %a = %a@." R.print x R.print y;
	       let p, v = AC.orient x y in 
	       let eqs = AC.solve p v in
	       L.fold_left Env.guarded (envi,cps) eqs
	     end
	)(env4,cp) ac_repl
    in 
    env5 , cp ,(p,touched,v)::res2

  and union_cp dep (env,res) eqs = 
    L.fold_left
      (fun (env,res) (x,y) ->
	 let env,rx = Env.ac_init env x in
	 let env,ry = Env.ac_init env y in
	 if debug_ac then 
	   printf "[AC] union_cp: %a = %a@." R.print rx R.print ry;
	 let new_env , new_res = union env rx ry dep in
	 new_env , new_res @ res
      )(env,res) eqs

  and union_repl dep (env,res) eqs = 
    L.fold_left
      (fun (env,res) (x,y) ->
	 let env,ry = Env.ac_init env y in
	 if debug_ac then 
	   printf "[AC] union_list: %a = %a@." R.print x R.print ry;
	 let new_env , new_res = union env x ry dep in
	 new_env , new_res @ res
      )(env,res) eqs

  let make_distinct env r1 r2 dep = 
    let d1 = try MapR.find r1 env.neqs with Not_found -> MapR.empty in
    let d2 = try MapR.find r2 env.neqs with Not_found -> MapR.empty in
    let neqs = 
      if MapR.mem r2 d1 then env.neqs else 
	MapR.add r1 (MapR.add r2 dep d1) 
	  (MapR.add r2 (MapR.add r1 dep d2) env.neqs) 
    in
    { env with neqs = neqs}

  let rec distinct env t1 t2 dep = 
    if debug_uf then 
      printf "@{<C.Bold>[UF]@} distinct %a <> %a@." T.print t1 T.print t2;
    let env = add (add env t1) t2 in
    let {re=r1 ; ex=ex1} = find env t1 in
    let {re=r2 ; ex=ex2} = find env t2 in
    let dep' = Ex.union ex1 (Ex.union ex2 dep) in
    if debug_uf then 
      begin
      printf "[UF] repr ( %a ) = %a@." T.print t1 R.print r1;
      printf "[UF] repr ( %a ) = %a@." T.print t2 R.print r2
      end;

    if R.compare r1 r2 = 0 then raise Inconsistent;
    let env = make_distinct env r1 r2 dep' in
    match Term.view t1,Term.view t2 with
      | {Term.f = f1; xs = [a]},{Term.f = f2; xs = [b]}
          when (Symbols.equal f1 f2 
                && R.compare (R.term_embed t1) r1 = 0 
              && R.compare (R.term_embed t2) r2 = 0) 
            -> distinct env a b dep
      | _,_ -> 
	  match (try R.solve r1 r2 with Unsolvable -> []) with
	      [a,b] -> make_distinct env a b dep'
            | _     -> env
      
  let equal env t1 t2 = R.compare (find env t1).re (find env t2).re = 0

  let are_in_neqs env r1 r2 = 
    (try MapR.mem r1 (MapR.find r2 env.neqs) with Not_found -> false) ||
    (try MapR.mem r2 (MapR.find r1 env.neqs) with Not_found -> false)

  let are_distinct env t1 t2 = 
    let b= 
      let m = add (add env t1) t2 in
      let r1 = (find m t1).re in
      let r2 = (find m t2).re in
      if R.compare r1 r2 = 0 then false
      else
	are_in_neqs env r1 r2 ||
          try 
	    L.exists 
	      (fun (a,b) -> are_in_neqs env a b) 
	      (R.solve r1 r2)
            (* True because r1=r2 <-> /\_{(a,b)in(R.solve r1 r2)}  a=b *)
          with Unsolvable -> true
(*      try
	match T.view t1 , T.view t2 with
	    {T.f=S.Int n1} , {T.f=S.Int n2} -> Hstring.compare n1 n2 <> 0
	  | _ -> 
	      let nt1 = MapR.find (find m t1) m.neqs in
	      let nt2 = MapR.find (find m t2) m.neqs in
	      SetT.mem t1 nt2 || SetT.mem t2 nt1
      with Not_found -> false*)
    in     
    if debug_uf then
      printf "@{<C.Bold>[UF]@} are_distinct %a<>%a ? %b@." 
	T.print t1 T.print t2 b; 
    b

  let explain env t1 t2 = 
    if Term.equal t1 t2 then Ex.empty
    else
      let {re=r1 ; ex=ex1} = MapR.find (MapT.find t1 env.make) env.repr in
      let {re=r2 ; ex=ex2} = MapR.find (MapT.find t2 env.make) env.repr in
      if R.compare r1 r2 = 0 then Ex.union ex1 ex2 
      else raise NotCongruent

  let neq_explain env t1 t2 = 
    let {re=r1 ; ex=ex1} = find env t1 in
    let {re=r2 ; ex=ex2} = find env t2 in
    if R.compare r1 r2 <> 0 then Ex.union ex1 ex2 
    else raise NotCongruent
    
  let find env t = (find env t).re

  let class_of env t = try 
    SetT.elements (MapR.find (find env t) env.classes)
  with Not_found -> [t]


end
