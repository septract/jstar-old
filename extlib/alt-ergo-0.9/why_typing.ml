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

open Options
open Format
open Why_ptree

module T = Term
module F = Formula
module A = Literal
module M = Map.Make(String)
module S = Set.Make(String)
module Sy = Symbols.Set
module I = Set.Make(struct type t=int let compare=Pervasives.compare end)
module H = Heap.Imperative(T)


module STRS = Set.Make(
  struct
    type t = Why_ptree.tterm * Sy.t * I.t

    let rec compare_term t1 t2 = match t1.tt_desc,t2.tt_desc with
      | TTvar s1 , TTvar s2 -> Symbols.compare s1 s2
      | TTapp (s1,l1) , TTapp(s2,l2) ->
	  let c = Symbols.compare s1 s2 in
	  if c=0 then compare_list l1 l2 else c
      | TTinfix(a1,s1,b1) , TTinfix(a2,s2,b2) ->
	  let c = Symbols.compare s1 s2 in
	  if c=0 then 
	    let c=compare_term a1 b1 in if c=0 then compare_term a2 b2 else c
	  else c
      | x , y -> Pervasives.compare x y
    and compare_list l1 l2 = match l1,l2 with
      [] , _ -> -1
    | _ , [] -> 1
    | x::l1 , y::l2 -> 
	let c = compare x y in if c=0 then compare_list l1 l2 else c

    let compare (t1,_,_) (t2,_,_) = compare_term t1 t2
  end)

type tdecl = 
    Assume of F.t * loc * bool 
  | PredDef of F.t * loc
  | Query of string * F.t * Literal.t list * loc

type error = 
  | BitvExtract of int*int
  | BitvExtractRange of int*int
  | ClashType of string
  | ClashParam of string
  | TypeBadArityDecl
  | UnknownType of string
  | WrongArity of string * int
  | SymbAlreadyDefined of string 
  | SymbUndefined of string
  | NotAPropVar of string
  | NotAPredicate of string
  | Unification of Ty.t * Ty.t
  | ShouldBeApply of string
  | WrongNumberofArgs of string
  | ShouldHaveType of Ty.t * Ty.t
  | ShouldHaveTypeIntorReal of Ty.t
  | ShouldHaveTypeBitv of Ty.t
  | ShouldHaveTypeProp
  | Notrigger 
  | CannotGeneralize
  | SyntaxError

let report fmt = function
  | BitvExtract(i,j) -> 
      fprintf fmt "bitvector extraction malformed (%d>%d)" i j
  | BitvExtractRange(n,j) -> 
      fprintf fmt "extraction out of range (%d>%d)" j n
  | ClashType s -> fprintf fmt "the type %s is already defined" s
  | ClashParam s -> fprintf fmt "parameter %s is bound twice" s
  | CannotGeneralize -> 
      fprintf fmt "cannot generalize the type of this expression"
  | TypeBadArityDecl -> fprintf fmt "bad arity declaration"
  | UnknownType s -> fprintf fmt "unknown type %s" s
  | WrongArity(s,n) -> fprintf fmt "the type %s has %d arguments" s n
  | SymbAlreadyDefined s -> fprintf fmt "the symbol %s is already defined" s
  | SymbUndefined s -> fprintf fmt "undefined symbol %s" s
  | NotAPropVar s -> fprintf fmt "%s is not a propositional variable" s
  | NotAPredicate s -> fprintf fmt "%s is not a predicate" s
  | Unification(t1,t2) ->
      fprintf fmt "%a and %a cannot be unified" Ty.print t1 Ty.print t2
  | ShouldBeApply s -> 
      fprintf fmt "%s is a function symbol, it should be apply" s
  | WrongNumberofArgs s ->
      fprintf fmt "Wrong number of arguments when applying %s" s
  | ShouldHaveType(ty1,ty2) ->
      fprintf fmt "this expression has type %a but is here used with type %a"
	Ty.print ty1 Ty.print ty2
  | ShouldHaveTypeBitv t -> 
      fprintf fmt "this expression has type %a but it should be a bitvector"
	Ty.print t
  | ShouldHaveTypeIntorReal t ->
      fprintf fmt 
	"this expression has type %a but it should have type int or real"
	Ty.print t
  | ShouldHaveTypeProp -> fprintf fmt "this expression should have type prop"
  | Notrigger -> fprintf fmt "No trigger for this lemma"
  | SyntaxError -> fprintf fmt "syntax error"

exception Error of error * loc
exception Warning of error * loc

let error e l = raise (Error(e,l))
let warning e l = raise (Warning(e,l))

let rec print_term fmt t = match t.tt_desc with
  | TTtrue -> fprintf fmt "true"
  | TTfalse -> fprintf fmt "false"
  | TTconst _ -> fprintf fmt "cst"
  | TTvar s -> fprintf fmt "%a" Symbols.print s
  | TTapp(s,l) -> 
      fprintf fmt "%a(%a)" Symbols.print s print_list l
  | TTinfix(t1,s,t2) -> 
      fprintf fmt "%a %a %a" print_term t1 Symbols.print s print_term t2
and print_list fmt = List.iter (fprintf fmt "%a," print_term)

module Types = struct

  let types = Hashtbl.create 97

  let is_type = Hashtbl.mem types

  let clear () = Hashtbl.clear types

  let bad_arity =
    let rec check s = function
      | [] -> false
      | v :: l -> S.mem v s || check (S.add v s) l
    in
    check S.empty
      
  let add v id loc = 
    if is_type id then error (ClashType id) loc;
    if bad_arity v then error TypeBadArityDecl loc;
    Hashtbl.add types id (List.length v)
      
  let valid v s loc = try
    let n = Hashtbl.find types s in
    if List.length v <> n  then error (WrongArity(s,n)) loc
  with Not_found -> error (UnknownType s) loc
    
end

module Profile = struct

  type t = Ty.t list * Ty.t

  let of_logictype p = 
    let htbl = Hashtbl.create 17 in
    let rec of_puretype = function
      | PPTint -> Ty.Tint
      | PPTbool -> Ty.Tbool
      | PPTreal -> Ty.Trat
      | PPTunit -> Ty.tunit
      | PPTbitv n -> Ty.Tbitv n
      | PPTvarid(s,_) -> 
	  (try Ty.Tvar(Hashtbl.find htbl s)
	   with Not_found-> 
	     let nv = Ty.fresh_var () in
	     Hashtbl.add htbl s nv;
	     Ty.Tvar nv)
      | PPTexternal (l,s,loc) -> 
	  Types.valid l s loc;
	  Ty.text (List.map of_puretype l) s
    in
    match p with
	PPredicate l -> List.map of_puretype l , Ty.Tbool
      | PFunction([],PPTvarid(_,loc)) -> 
	  error CannotGeneralize loc
      | PFunction(l,t) -> List.map of_puretype l , of_puretype t

  (* create fresh type variables each time it is called *)
  let fresh (l,ty) = 
    let hvars = Hashtbl.create 17 in
    let rec freshrec = function
      | Ty.Tvar {Ty.v=x} -> 
	  (try Ty.Tvar(Hashtbl.find hvars x) 
	   with Not_found -> 
	     let nv = Ty.fresh_var() in 
	     Hashtbl.add hvars x nv; Ty.Tvar nv)
      | Ty.Text(l,s) -> Ty.Text(List.map freshrec l,s)
      | t -> t
    in
    List.map (fun t->freshrec (Ty.shorten t)) l , freshrec (Ty.shorten ty)

end

module Decl = struct
  let queue = Queue.create ()

  let clear () = Queue.clear queue

  let varset_of_list = 
    List.fold_left 
      (fun acc (s,ty) -> 
	 Term.Set.add (Term.make s [] (Ty.shorten ty)) acc) Term.Set.empty

  let rec make_term { tt_ty = ty; tt_desc = tt } = 
    let ty = Ty.shorten ty in
    match tt with
      | TTtrue -> T.vrai
      | TTfalse -> T.faux
      | TTconst (Tint i) -> T.int i
      | TTconst (Treal r) -> T.rat r
      | TTconst (Tnum n) -> T.rat (Num.string_of_num n)
      | TTconst (Tbitv bt) -> T.bitv bt ty
      | TTconst Tunit -> T.unit
      | TTvar s ->  T.make s [] ty 
      | TTapp (s,l) -> T.make s (List.map make_term l) ty
      | TTinfix (t1,s,t2) ->  T.make s [make_term t1;make_term t2] ty

  let make_form name f = 
    let rec make_form acc = function
      | TFatom a ->
	  let a , lit = match a with
	      TAtrue -> 
		A.vrai , A.vrai::acc
	    | TAfalse -> 
		A.faux , A.faux::acc
	    | TAeq [t1;t2] -> 
		let lit = A.make (A.Eq(make_term t1,make_term t2)) in
		lit , lit::acc
	    | TApred t ->
		let lit = A.mk_pred (make_term t) in
		lit , lit::acc
	    | TAneq [t1;t2] -> 
		let lit = A.make (A.Neq(make_term t1,make_term t2)) in
		lit , lit::acc
	    | TAle [t1;t2] -> 
		(try 
		   let ale = Builtin.is_builtin "<=" in
		   let lit = 
		     A.make (A.Builtin(true,ale,[make_term t1;make_term t2]))
		   in lit , lit::acc
		 with Not_found -> assert false)
	    | TAlt [t1;t2] ->  
		(try 
		   let alt = Builtin.is_builtin "<" in
		   let lit = 
		     A.make (A.Builtin(true,alt,[make_term t1;make_term t2])) 
		   in lit , lit::acc
		 with Not_found -> assert false)
	    | TAbuilt(n,lt) ->
		let lit = A.make (A.Builtin(true,n,List.map make_term lt)) in
		lit , lit::acc
	    | _ -> assert false
	  in F.mk_lit a , lit
      | TFop((OPand | OPor) as op,[f1;f2]) -> 
	  let ff1 , lit1 = make_form acc f1 in
	  let ff2 , lit2 = make_form lit1 f2 in
	  let op = match op with OPand -> F.mk_and | _ -> F.mk_or in
	  op ff1 ff2 , lit2
      | TFop(OPimp,[f1;f2]) -> 
	  let ff1 , _ = make_form acc f1 in
	  let ff2 , lit = make_form acc f2 in
	  F.mk_imp ff1 ff2 , lit
      | TFop(OPnot,[f]) -> 
	  let ff , lit = make_form acc f in
	  F.mk_not ff , lit
      | TFop(OPif t,[f2;f3]) -> 
	  let tt = make_term t in
	  let ff2 , lit2 = make_form acc f2 in
	  let ff3 , lit3 = make_form lit2 f3 in
	  F.mk_if  tt ff2 ff3 , lit3
      | TFop(OPiff,[f1;f2]) -> 
	  let ff1 , lit1 = make_form acc f1 in
	  let ff2 , lit2 = make_form lit1 f2 in
	  F.mk_iff ff1 ff2 , lit2
      | (TFforall qf | TFexists qf) as f -> 
	  let bvars = varset_of_list qf.qf_bvars in
	  let upvars = varset_of_list qf.qf_upvars in
	  let trs = List.map (List.map make_term) qf.qf_triggers in
	  let ff , lit = make_form acc qf.qf_form in
	  let fh = 
	    match f with
	      | TFforall _ -> F.mk_forall upvars bvars trs ff name
	      | TFexists _ -> F.mk_exists upvars bvars trs ff name
	      | _ -> assert false
	  in fh , lit
      | TFlet (up,lvar,lterm,lf) -> let ff, lit = make_form acc lf in
            F.mk_let (varset_of_list up) lvar (make_term lterm) ff, lit
      | _ -> assert false
    in
    make_form [] f

  let push_assume f name loc match_flag = 
    let ff , _ = make_form name f in
    Queue.push (Assume(ff,loc,match_flag)) queue

  let push_preddef f name loc match_flag = 
    let ff , _ = make_form name f in
    Queue.push (PredDef(ff,loc)) queue
      
  let push_query n f loc = 
    let ff, lits = make_form "" f in
    Queue.push (Query(n,ff,lits,loc)) queue

end

module Logics = struct
  type t = Symbols.t * Profile.t

  let logics : (string,t) Hashtbl.t = Hashtbl.create 97
    
  let clear () = Hashtbl.clear logics

  let add pf loc ac n = 
    let sy = Symbols.name n ~ac:ac in
    if Hashtbl.mem logics n then error (SymbAlreadyDefined n) loc;
    Hashtbl.add logics n (sy,pf)

  let fresh n loc = try
      let s , ty = Hashtbl.find logics n in 
      s , Profile.fresh ty
  with Not_found -> error (SymbUndefined n) loc

end
    
module Env = struct

  type t = { 
    var_map : (Symbols.t * Ty.t) M.t ; (* variables' map*)
    tvar_map : Ty.t M.t ; (* typed variables' map *)
  }

  let empty = { var_map = M.empty ;  tvar_map = M.empty }

  let rec of_puretype tvmap create_var = function
    | PPTint -> Ty.Tint , tvmap
    | PPTbool -> Ty.Tbool , tvmap
    | PPTreal -> Ty.Trat , tvmap
    | PPTunit -> Ty.tunit , tvmap 
    | PPTbitv n -> Ty.Tbitv n , tvmap 
    | PPTvarid(s,_) -> 
	(try M.find s tvmap , tvmap
	 with Not_found-> 
	   let nv =  create_var() in nv , M.add s nv tvmap)
    | PPTexternal (l,s,loc) -> 
	Types.valid l s loc;
	let tvmap , l = 
	  List.fold_left 
	    (fun (tvmap,l) t -> 
	       let ty , tvmap  = of_puretype tvmap create_var t in
	       tvmap , ty::l) (tvmap,[]) l 
	in
	Ty.text (List.rev l) s , tvmap

  let add create_symb create_var =
    List.fold_left
      (fun env (l,pty) ->
	 let ty , tvmap = of_puretype env.tvar_map create_var pty in
	 List.fold_left 
	   (fun env x ->
	      let sx = create_symb x in
	      { env with var_map = M.add x (sx,ty) env.var_map})
	   { env with tvar_map = tvmap } l)

  let add_var = add Symbols.var (fun () -> Ty.Tvar (Ty.fresh_var ()))

  let add_name = add Symbols.name Ty.fresh_empty_text

  let find {var_map=m} n = M.find n m

  let mem n {var_map=m} = M.mem n m

  let list_of {var_map=m} = M.fold (fun _ c acc -> c::acc) m []
      
end

module Triggers = struct

  let sort = 
    List.sort (fun l1 l2 -> compare (List.length l1) (List.length l2) )
      
  let at_most =
    let rec atmost acc n l = 
      match n , l with
	| 1 , x::_ -> x::acc
	| _ , x::l -> atmost (x::acc) (n-1) l
	| _ , [] -> acc
    in fun n l -> atmost [] n l

  let is_var t = match t.tt_desc with
    | TTvar _ -> true
    | TTapp (_,l) -> l=[]
    | _ -> false

  let parties = 
    let rec parties_rec llt (bv,vty) = function
	[] -> llt
      | (t,bv1,vty1)::l -> 
	  let llt = 
	    List.fold_left
	      (fun llt (l,bv2,vty2)->
		 let lt , bv3 , vty3 = 
		   t::l , Sy.union bv2 bv1 , I.union vty2 vty1 in 
		 (lt , bv3 , vty3)::llt) 
	      llt llt in
	  parties_rec (([t],bv1,vty1)::llt) (bv,vty) l
    in parties_rec []
	 
  let strict_subset bv vty = 
    List.exists 
      (fun (_,bv',vty') -> 
	 (Sy.subset bv bv' && not(Sy.equal bv bv')  && I.subset vty vty') 
	 or (I.subset vty vty' && not(I.equal vty vty') && Sy.subset bv bv') )

  let simplification (bv_a,vty_a) = 
    let rec simpl_rec acc = function
	[] -> acc
      | ((t,bv,vty) as e)::l -> 
	  if strict_subset bv vty l or strict_subset bv vty acc or
	    (Sy.subset bv_a bv && I.subset vty_a vty) or
	    (Sy.equal (Sy.inter bv_a bv) Sy.empty &&
	       I.equal (I.inter vty_a vty) I.empty)
	  then simpl_rec acc l
	  else  simpl_rec (e::acc) l
    in simpl_rec []

  let rec vars_of_term bv acc t = match t.tt_desc with
    | TTvar x -> if Sy.mem x bv then Sy.add x acc else acc
    | TTapp (_,lt) -> List.fold_left (vars_of_term bv) acc lt
    | TTinfix (t1,_,t2) -> List.fold_left (vars_of_term bv) acc [t1;t2]
    | _ -> acc

  let underscoring_term mvars underscores t = 
    let rec under_rec t =  
      { t with tt_desc = under_rec_desc t.tt_desc}
    and under_rec_desc t = match t with
	| TTvar x when Sy.mem x mvars -> 
	    if not (Sy.mem x !underscores) then 
	      (	underscores := Sy.add x !underscores; t)
	    else 
		TTvar (Symbols.underscoring x)
	| TTvar _ -> t
	| TTapp (s,lt) -> TTapp(s,List.map under_rec lt)
	| TTinfix (t1,op,t2) -> TTinfix(under_rec t1,op,under_rec t2)
	| _ -> t
    in 
    under_rec t

  let underscoring_mt bv mt = 
    let vars , mvars = 
      List.fold_left 
	(fun (vars,mvars) t -> 
	   let vs = vars_of_term bv Sy.empty t in
	   let mvars = Sy.union mvars (Sy.inter vars vs) in
	   Sy.union vars vs , mvars) (Sy.empty,Sy.empty) mt in
    let underscores = ref Sy.empty in
    List.map (underscoring_term mvars underscores) mt
    
  let multi_triggers gopt (bv,vty) trs =
    let terms = simplification (bv,vty) trs in
    let l_parties = parties (bv,vty) terms  in 
    let lm = 
      List.fold_left 
	(fun acc (lt,bv',vty') -> 
	   if Sy.subset bv bv' && I.subset vty vty' then lt::acc else acc) 
	[] l_parties
    in
    let mv , mt = List.partition (List.exists is_var) lm in
    let mv , mt = sort mv , sort mt in
    let m = at_most redondance (if gopt then (mt@mv) else mt) in
    (*(List.map (underscoring_mt bv) m)@
      (List.map (underscoring_mt bv) (List.map List.rev m))*)
    at_most redondance m 

  let rec vty_ty acc t = 
    let t = Ty.shorten t in
    match t with
      | Ty.Tvar { Ty.v = i ; value = None } -> I.add i acc 
      | Ty.Text(l,_) -> List.fold_left vty_ty acc l
      | _ -> acc
    
  let rec vty_term acc t = 
    let acc = vty_ty acc t.tt_ty in
    match t.tt_desc with
      | TTapp (_,l) -> List.fold_left vty_term acc l
      | TTinfix (t1,_,t2) -> vty_term (vty_term acc t1) t2
      | _ -> acc

  let rec vty_form acc = function
    | TFatom(TAeq l | TAneq l | TAle l | TAlt l | TAbuilt(_,l))-> 
	List.fold_left vty_term acc l
    | TFatom TApred t -> vty_term acc t
    | TFop(_,l) -> List.fold_left vty_form acc l
    | _ -> acc (* we don't go through quantifiers *)

  let csort = Symbols.name "c_sort"

  let filter_mono (bv,vty) (t,bv_t,vty_t) = 
    Sy.subset bv bv_t && I.subset vty vty_t && 
      match t.tt_desc with
	| TTapp(s,_) -> 
	    not (Symbols.equal s csort)
	| _ -> true
      

  let as_bv bv s = not (Sy.is_empty (Sy.inter bv s))
  let as_tyv vty s = not (I.is_empty (I.inter vty s))

  let potential_triggers = 
    let rec potential_rec ((bv,vty) as vars) acc t = 
      match t.tt_desc with
	| TTvar x ->
	    let vty_t = vty_term I.empty t in
	    if Sy.mem x bv or as_tyv vty vty_t then
	      STRS.add (t,Sy.singleton x, vty_t) acc
	    else acc
	| TTapp(s,lf)-> 
	    let vty_lf = List.fold_left vty_term I.empty lf in
	    let bv_lf = List.fold_left (vars_of_term bv) Sy.empty lf in
	    if as_bv bv bv_lf or as_tyv vty vty_lf then
	      List.fold_left (potential_rec vars) 
		(STRS.add (t,bv_lf,vty_lf) acc) lf
	    else acc
	| TTinfix(t1,_,t2) -> 
	    let vty_lf = List.fold_left vty_term I.empty [t1;t2] in
	    let bv_lf = List.fold_left (vars_of_term bv) Sy.empty [t1;t2] in
	    if as_bv bv bv_lf or as_tyv vty vty_lf then
	      List.fold_left (potential_rec vars) 
		(STRS.add (t,bv_lf,vty_lf) acc) (*acc*) [t1;t2]
	    else acc
	| _ -> acc
    in fun vars -> List.fold_left (potential_rec vars) STRS.empty

  let filter_good_triggers (bv,vty) = 
    List.filter 
      (fun l ->
	 let s1 = List.fold_left (vars_of_term bv) Sy.empty l in
	 let s2 = List.fold_left vty_term I.empty l in
	 Sy.subset bv s1 && I.subset vty s2)

  let make_triggers gopt vars trs = 
    match List.filter (filter_mono vars) trs with
	[] -> 
	  multi_triggers gopt vars trs
      | trs' -> 
	  let f l = at_most redondance (List.map (fun (t,_,_) -> [t]) l) in
	  let trs_v, trs_nv = 
	    List.partition (fun (t,_,_) -> is_var t) trs' in
	  let ll = 
	    if trs_nv=[] then
	      if triggers_var || gopt then 
		f trs_v else [](*multi_triggers vars trs*)
	    else f trs_nv 
	  in 
	  if glouton then ll@(multi_triggers gopt vars trs) else ll

  let rec make_rec gopt ((bv,vty) as vars) f loc = match f with
    | TFatom (TAfalse | TAtrue) ->
	f , STRS.empty
    | TFatom a ->
	if Sy.is_empty bv && I.is_empty vty then f , STRS.empty
	else 
	  begin
	    let l = 
	      match a with    
		  TAeq l | TAneq l | TAle l | TAlt l | TAbuilt(_,l) -> l
		| TApred t -> [t]
		| _ -> assert false
	    in
	    f , potential_triggers vars l
	  end
    | TFop(op,lf) -> 
	let lf , trs = 
	  List.fold_right
	    (fun f (lf,trs1) ->
	       let f , trs2 = make_rec gopt vars f loc in
	       f::lf , STRS.union trs1 trs2) lf ([],STRS.empty) in
	TFop(op,lf) , trs

    | TFforall ({ qf_form=TFop(OPiff,[TFatom _ as f1;f2])} as qf) -> 

	let vty' = vty_form I.empty qf.qf_form in
	let bv' = 
	  List.fold_left (fun b (s,_) -> Sy.add s b) Sy.empty qf.qf_bvars in

	let u = Sy.union bv bv' , I.union vty vty' in
	let f1' , trs1 = make_rec gopt u f1 loc in
	let f2' , trs2 = make_rec gopt u f2 loc in

	let trs12 = 
	  if Options.notriggers || qf.qf_triggers=[] then
	    (make_triggers false (bv',vty') (STRS.elements trs1))@
	      (make_triggers false (bv',vty') (STRS.elements trs2))
	  else filter_good_triggers (bv',vty') qf.qf_triggers
	in

	let trs = 
	  STRS.filter 
	    (fun (_,bvt,_) -> Sy.is_empty (Sy.inter bvt bv')) 
	    (STRS.union trs1 trs2) in

	let r  = { qf with 
		     qf_triggers = trs12 ; 
		     qf_form = TFop(OPiff,[f1'; f2'])}
	in
	(match f with TFforall _ -> TFforall r , trs | _ -> TFexists r , trs)


    | TFforall qf | TFexists qf -> 
	let vty' = vty_form I.empty qf.qf_form in
	let bv' = 
	  List.fold_left (fun b (s,_) -> Sy.add s b) Sy.empty qf.qf_bvars in
	let f' , trs = 
	  make_rec gopt (Sy.union bv bv',I.union vty vty') qf.qf_form loc in
	let trs' = 
	  if Options.notriggers || qf.qf_triggers=[] then
	    make_triggers gopt (bv',vty') (STRS.elements trs)
	  else filter_good_triggers (bv',vty') qf.qf_triggers
	in
	let trs = 
	  STRS.filter (fun (_,bvt,_) -> Sy.is_empty (Sy.inter bvt bv')) trs in
	let r  = {qf with qf_triggers = trs' ; qf_form = f'} in
	(match f with TFforall _ -> TFforall r , trs | _ -> TFexists r , trs)


    | TFlet (up,v,t,f) -> let f,trs = make_rec gopt vars f loc in 
        TFlet (up,v,t,f),trs

	
  let make gopt f loc = match f with
    | TFforall _ | TFexists _ -> fst(make_rec gopt (Sy.empty,I.empty) f loc)
    | _  ->  
	let vty = vty_form I.empty f in
	let f , trs = make_rec gopt (Sy.empty,vty) f loc in
	if I.is_empty vty then f
	else 
	  let trs = STRS.elements trs in
	  let trs = make_triggers gopt (Sy.empty,vty) trs in
	  if trs=[] then warning Notrigger loc;
	  TFforall 
	    {qf_bvars=[]; qf_upvars=[]; qf_triggers=trs; qf_form=f }

  let print fmt =  List.iter (fprintf fmt "%a | " T.print_list) 
      
end

let rec freevars_term acc t = match t.tt_desc with
  | TTvar x -> Sy.add x acc
  | TTapp (_,lt) -> List.fold_left freevars_term acc lt
  | TTinfix (t1,_,t2) -> List.fold_left freevars_term acc [t1;t2]
  | _ -> acc
      
let freevars_atom = function
  | TAeq lt | TAneq lt | TAle lt | TAlt lt | TAbuilt(_,lt) ->
      List.fold_left freevars_term Sy.empty lt
  | TApred t -> freevars_term  Sy.empty t
  | _ -> Sy.empty
      
let rec freevars_form = function
  | TFatom a -> freevars_atom a
  | TFop (_,lf) -> List.fold_left Sy.union Sy.empty (List.map freevars_form lf)
  | TFforall qf | TFexists qf -> 
      let s = freevars_form qf.qf_form in
      List.fold_left (fun acc (s,_) -> Sy.remove s acc) s qf.qf_bvars
  | TFlet (up,v,t,f) -> freevars_term (Sy.remove v (freevars_form f)) t

let symbol_of = function
    PPadd -> Symbols.plus
  | PPsub -> Symbols.minus
  | PPmul -> Symbols.mult
  | PPdiv -> Symbols.div
  | PPmod ->  Symbols.modulo
  | PPat -> Symbols.at
  | _ -> assert false  

let rec type_term env f = 
  let e,t = type_term_desc env f.pp_loc f.pp_desc in
  { tt_desc = e ; tt_ty = t }

and type_term_desc env loc = function
  | PPtrue -> TTtrue , Ty.Tbool
  | PPfalse -> TTfalse , Ty.Tbool
  | PPconst (ConstInt n) -> TTconst(Tint n) , Ty.Tint
  | PPconst (ConstReal n) -> TTconst(Treal n) , Ty.Trat
  | PPconst (ConstNum n) -> TTconst(Tnum n) , Ty.Trat
  | PPconst ConstUnit -> TTconst Tunit , Ty.tunit
  | PPconst (ConstBitv n) -> TTconst(Tbitv n) , Ty.Tbitv (String.length n)
  | PPvar p -> 
      begin
	try let s,t = Env.find env p in TTvar s , t
	with Not_found -> 
	  match Logics.fresh p loc with
	      s , ([], ty) -> TTvar s , ty 
	    | _ -> error (ShouldBeApply p) loc
      end
  | PPapp("^",[e;{pp_desc=PPconst(ConstInt i)} as ei;
	       {pp_desc=PPconst(ConstInt j)} as ej]) ->
      begin
	let te = type_term env e in
	let tye = Ty.shorten te.tt_ty in
	let i = int_of_string i in
	let j = int_of_string j in
	match tye with
	    Ty.Tbitv n -> 
	      if i>j then error (BitvExtract(i,j)) loc;
	      if j>=n then error (BitvExtractRange(n,j) ) loc;
	      let tei = type_term env ei in
	      let tej = type_term env ej in
	      TTapp(Symbols.shat,[te;tei;tej]) , Ty.Tbitv (j-i+1)
	  | _ -> error (ShouldHaveType(tye,Ty.Tbitv (j+1))) loc
      end
  | PPapp(p,args) -> 
      begin
	let te_args = List.map (type_term env) args in
	let lt_args =  List.map (fun {tt_ty=t} -> t) te_args in
	let s , (lt,t) = Logics.fresh p loc in
	try
	  List.iter2 Ty.unify lt lt_args; 
	  TTapp(s,te_args) , t
	with 
	    Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) loc
	  | Invalid_argument _ -> error (WrongNumberofArgs p) loc
      end
  | PPinfix(t1,PPat,t2) ->
      begin
	let s = symbol_of PPat in
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.tt_ty in
	let ty2 = Ty.shorten te2.tt_ty in
	match ty1,ty2 with
	    Ty.Tbitv n , Ty.Tbitv m -> TTinfix(te1,s,te2) , Ty.Tbitv (n+m)
	  | Ty.Tbitv _ , _ -> error (ShouldHaveTypeBitv ty2) t2.pp_loc
	  | _ , Ty.Tbitv _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
	  | _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
      end
  | PPinfix(t1,(PPadd | PPsub | PPmul | PPdiv | PPmod as op),t2) ->
      begin
	let s = symbol_of op in
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.tt_ty in
	let ty2 = Ty.shorten te2.tt_ty in
	match ty1,ty2 with
	    Ty.Tint , Ty.Tint -> TTinfix(te1,s,te2) , ty1
	  | Ty.Trat , Ty.Trat -> TTinfix(te1,s,te2), ty2
	  | Ty.Tint , _ -> error (ShouldHaveType(ty2,Ty.Tint)) t2.pp_loc
	  | Ty.Trat , _ -> error (ShouldHaveType(ty2,Ty.Trat)) t2.pp_loc
	  | _ -> error (ShouldHaveTypeIntorReal ty1) t1.pp_loc
      end
  | PPprefix(PPneg, {pp_desc=PPconst (ConstInt n)}) -> 
      TTconst(Tint ("-"^n)) , Ty.Tint
  | PPprefix(PPneg, {pp_desc=PPconst (ConstReal n)}) -> 
      TTconst(Treal ("-"^n)) , Ty.Trat
  | PPprefix(PPneg, {pp_desc=PPconst (ConstNum n)}) -> 
      TTconst(Tnum (Num.minus_num n)) , Ty.Trat
  | PPprefix(PPneg, e) -> 
      begin
	let te = type_term env e in
	let ty = Ty.shorten te.tt_ty in
	match ty with
	    Ty.Tint -> 
	      let z = TTconst(Tint "0") in 
	      TTinfix({tt_desc=z ; tt_ty=Ty.Tint},Symbols.minus,te) , Ty.Tint
	  | Ty.Trat -> 
	      let z = TTconst(Treal "0") in 
	      TTinfix({tt_desc=z ;tt_ty=Ty.Trat},Symbols.minus,te) , Ty.Trat
	  | _ -> error (ShouldHaveTypeIntorReal ty) e.pp_loc
      end
  | PPif(t1,t2,t3) ->
      begin
	let te1 = type_term env t1 in
	let ty1 = Ty.shorten te1.tt_ty in
	if not (Ty.equal ty1 Ty.Tbool) then 
	  error (ShouldHaveType(ty1,Ty.Tbool)) t1.pp_loc;
	let te2 = type_term env t2 in
	let te3 = type_term env t3 in
	let ty2 = Ty.shorten te2.tt_ty in
	let ty3 = Ty.shorten te3.tt_ty in
	if not (Ty.equal ty2 ty3) then
	  error (ShouldHaveType(ty3,ty2)) t3.pp_loc;
	TTapp(Symbols.name "ite",[te1;te2;te3]) , ty2
      end
  | PPnamed(_,t) -> 
      let t = type_term env t in
      t.tt_desc, t.tt_ty
  | _ -> error SyntaxError loc


let rec join_forall f = match f.pp_desc with
    PPforall(vs,ty,trs1,f) -> 
      let tyvars,trs2,f = join_forall f in  
      (vs,ty)::tyvars , trs1@trs2 , f
  | PPnamed(_,f) -> join_forall f
  | _ -> [] , [] , f

let rec join_exists f = match f.pp_desc with
    PPexists(x,ty,f) -> 
      let tyvars,f = join_exists f in  
      ([x],ty)::tyvars ,  f
  | PPnamed(_,f) -> join_exists f
  | _ -> [] , f

let make_le_or_lt p l = 
  let s = match p with PPle -> "<=" | PPlt -> "<" | _ -> assert false in
  try 
    let _ = Builtin.is_builtin s in 
    (match p with PPle -> TAle l | PPlt -> TAlt l | _ -> assert false)
  with Not_found -> 
    let s = Symbols.name s in (* XXX *)
    let t = {tt_desc=TTapp(s,l);tt_ty=Ty.Tbool} in 
    TAeq[t;{tt_desc=TTtrue;tt_ty=Ty.Tbool}]

let rec type_form env f = match f.pp_desc with
  | PPtrue -> TFatom TAtrue, Sy.empty
  | PPfalse -> TFatom TAfalse, Sy.empty
  | PPvar p ->
      let r = begin
	match Logics.fresh p f.pp_loc with
	    s, ([] ,Ty.Tbool) -> 
	      (try 
		 TFatom (TAbuilt(Builtin.is_builtin p,[]))
	       with Not_found -> 
		 let t1 = {tt_desc=TTvar s;tt_ty=Ty.Tbool} in
		 TFatom (TAeq [t1;{tt_desc=TTtrue;tt_ty=Ty.Tbool}]))
	  | _ -> error (NotAPropVar p) f.pp_loc
      end in r, freevars_form r
  | PPapp(p,args) ->
      let r = begin
	let te_args = List.map (type_term env) args in
	let lt_args =  List.map (fun {tt_ty=t} -> t) te_args in
	match Logics.fresh p f.pp_loc with
	    s , (lt,Ty.Tbool) -> 
	      begin
		try
		  List.iter2 Ty.unify lt lt_args;
		  (try 
		     TFatom (TAbuilt(Builtin.is_builtin p,te_args))
		   with Not_found -> 
		     let t1 = {tt_desc=TTapp(s,te_args);tt_ty=Ty.Tbool} in 
		     (*TFatom (TAeq[t1;{tt_desc=TTtrue;tt_ty=Ty.Tbool}])) *)
		     TFatom (TApred t1))
		with 
		    Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
		  | Invalid_argument _ -> error (WrongNumberofArgs p) f.pp_loc
	      end
	  | _ -> error (NotAPredicate p) f.pp_loc
      end in r, freevars_form r
  | PPinfix 
      ({pp_desc = PPinfix (_, (PPlt|PPle|PPgt|PPge|PPeq|PPneq), a)} as p, 
       (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      let r = 
        let q = { pp_desc = PPinfix (a, r, b); pp_loc = f.pp_loc } in
        let f1,_ = type_form env p in
        let f2,_ = type_form env q in
        TFop(OPand,[f1;f2])
      in r, freevars_form r
  | PPinfix(t1, (PPlt | PPgt | PPle | PPge | PPeq | PPneq as op) ,t2) -> 
      let r = begin
	let tt1 = type_term env t1 in
	let tt2 = type_term env t2 in
	try
	  Ty.unify tt1.tt_ty tt2.tt_ty;
	  match op with
	    | PPeq -> TFatom (TAeq [tt1;tt2])
	    | PPneq -> TFatom (TAneq [tt1;tt2])
	    | PPle -> TFatom (make_le_or_lt PPle [tt1;tt2])
	    | PPge -> TFatom (make_le_or_lt PPle [tt2;tt1])
	    | PPlt -> 
		begin
		  let ty = Ty.shorten tt1.tt_ty in
		  match ty with
		      Ty.Tint -> 
			let one = 
			  {tt_ty=Ty.Tint ; tt_desc=TTconst(Tint "1")} in
			let desc = TTinfix(tt2,Symbols.minus,one) in
			TFatom 
			  (make_le_or_lt PPle [tt1;{tt2 with tt_desc=desc}])
		    | _ -> 
			TFatom (make_le_or_lt PPlt [tt1;tt2])
		end
	    | PPgt -> 
		begin
		  let ty = Ty.shorten tt1.tt_ty in
		  match ty with
		      Ty.Tint ->
			let one = 
			  {tt_ty=Ty.Tint ; tt_desc=TTconst(Tint "1")} in
			let desc = TTinfix(tt1,Symbols.minus,one) in
			TFatom 
			  (make_le_or_lt PPle [tt2;{tt1 with tt_desc=desc}])
		    | _ -> TFatom (make_le_or_lt PPlt [tt2;tt1])
		end
	    | _ -> assert false
	with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
      end in r, freevars_form r
  | PPinfix(f1,op ,f2) -> 
      begin
	let f1,fv1 = type_form env f1 in
	let f2,fv2 = type_form env f2 in
	((match op with
	  | PPand -> TFop(OPand,[f1;f2])
	  | PPor -> TFop(OPor,[f1;f2])
	  | PPimplies -> TFop(OPimp,[f1;f2])
	  | PPiff ->TFop(OPiff,[f1;f2])
	  | _ -> assert false), Sy.union fv1 fv2)
      end
  | PPprefix(PPnot,f) -> 
      let f,fv = type_form env f in TFop(OPnot,[f]),fv
  | PPif(f1,f2,f3) -> 
      let f1 = type_term env f1 in
      let f2,fv2 = type_form env f2 in
      let f3,fv3 = type_form env f3 in
      TFop(OPif f1,[f2;f3]), Sy.union fv2 fv3
  | PPnamed(x,f) -> type_form env f
  | PPforall _ | PPexists _ ->
      let ty_vars,ty,triggers,f' = 
	match f.pp_desc with 
	    PPforall(vars,ty,triggers,f') -> 
	      let ty_vars , triggers' , f' = join_forall f' in
	      (vars,ty)::ty_vars , ty , triggers@triggers' , f'
	  | PPexists(x,ty,f') -> 
	      let ty_vars , f' = join_exists f' in
	      ([x],ty)::ty_vars , ty , [] , f'
	  | _ -> assert false
      in
      let env' = Env.add_var env ty_vars in
      let f',fv = type_form env' f' in
      let ty_triggers = List.map (List.map (type_term env')) triggers in
      let upbvars = Env.list_of env in
      let bvars = 
	List.fold_left 
	  (fun acc (l,_) -> 
	     let tys = List.map (Env.find env') l in
	     let tys = List.filter (fun (s,_) -> Sy.mem s fv) tys in
	     tys @ acc) [] ty_vars in 
      let qf_form = {
	qf_upvars = upbvars ; 
	qf_bvars = bvars ;
	qf_triggers = ty_triggers ;
	qf_form = f'}
      in
      (match f.pp_desc with 
	   PPforall _ -> TFforall qf_form  
	 | _ -> Existantial.make qf_form), 
      (List.fold_left (fun acc (l,_) -> Sy.remove l acc) fv bvars)
  | PPlet (var,t,f) -> 
      let {tt_ty=ttype} as tt = type_term env t in
      let svar = Symbols.var var in
      let up = Env.list_of env in
      let env = {env with 
		   Env.var_map = M.add var (svar,ttype) env.Env.var_map} in
      let f,fv = type_form env f in
        TFlet (up ,svar , tt, f), freevars_term (Sy.remove svar fv) tt
  | _ -> error ShouldHaveTypeProp f.pp_loc

let inv_infix = function PPand -> PPor | PPor -> PPand | _ -> assert(false)

let rec elim_toplevel_forall env bnot f = 
  (* bnot = true : nombre impaire de not *)
  match f.pp_desc with
      PPforall(lv,t,_,f) when bnot-> 
	elim_toplevel_forall (Env.add_name env [lv,t]) bnot f

    | PPexists(lv,t,f) when not bnot-> 
	elim_toplevel_forall (Env.add_name env [[lv],t]) bnot f

    | PPinfix(f1,PPand,f2) when not bnot -> 
	let env , f1 = elim_toplevel_forall env false f1 in
	let env , f2 = elim_toplevel_forall env false f2 in
	env , { f with pp_desc = PPinfix(f1, PPand , f2)}
	
    | PPinfix(f1, PPor,f2) when bnot -> 
	let env , f1 = elim_toplevel_forall env true f1 in
	let env , f2 = elim_toplevel_forall env true f2 in
        env , { f with pp_desc = PPinfix(f1, PPand , f2)}

    | PPinfix(f1,PPimplies,f2) when bnot -> 
        let env , f1 = elim_toplevel_forall env false f1 in
	let env , f2 = elim_toplevel_forall env true f2 in
	  env , { f with pp_desc = PPinfix(f1,PPand,f2)}
	
    | PPprefix(PPnot,f) -> elim_toplevel_forall env (not bnot) f

    | _ when bnot -> env , { f with pp_desc=PPprefix(PPnot,f)}

    | _  -> env , f


let rec intro_hypothesis env bnot f = 
  match f.pp_desc with
    | PPinfix(f1,PPimplies,f2) when bnot -> 
	let env , f1 = elim_toplevel_forall env (not bnot) f1 in
	let env , axioms , goal = intro_hypothesis env bnot f2 in
	env , f1::axioms , goal
    | PPforall(lv,t,_,f) when bnot ->  
	intro_hypothesis (Env.add_name env [lv,t]) bnot f

    | PPexists(lv,t,f) when not bnot-> 
	intro_hypothesis (Env.add_name env [[lv],t]) bnot f

    | _ -> 
	let env , f = elim_toplevel_forall env bnot f in
	env , [] , f

(*
let rec move_up f = 
  { f with pp_desc = move_up_desc f.pp_desc }

and move_up_desc = function
  | PPinfix(f1,op,f2) ->
      PPinfix(move_up f1,op,move_up f2)
	
  | PPprefix(op,f1) ->
      PPprefix(op,move_up f1)
	
  | PPif(f1,f2,f3) ->
      PPif(move_up f1, move_up f2, move_up f3)
	
  | PPforall(lv1,t1,[],
	     ({pp_desc=
		  PPinfix(fl,op,({pp_desc=PPforall(lv2,t2,[],f2)} as ff))} 
		as fd)) ->
      let ff = { ff with pp_desc = PPinfix(fl,op,f2)} in
      let fd = {fd with pp_desc=PPforall(lv2,t2,[],ff)} in
      PPforall(lv1,t1,[],fd)
	
    | f -> f
*)

let fresh_axiom_name = 
  let cpt = ref 0 in fun () -> incr cpt; "_H"^(string_of_int !cpt)

let rec make_pred loc trs f = function
    [] ->  f
  | [x,t] ->
      { pp_desc = PPforall([x],t,trs,f) ; pp_loc = loc }
  | (x,t)::l -> 
      { pp_desc = PPforall([x],t,[],(make_pred loc trs f l)) ; pp_loc = loc }

let check_duplicate_params l =
  let rec loop l acc =
    match l with
      | [] -> ()
      | (loc,x,_)::rem ->
	  if List.mem x acc then
	    error (ClashParam x) loc
	  else loop rem (x::acc)
  in
  loop l []

let type_decl acc d = 
  try
    match d with
	Logic (loc,ac, ext, lp, ty) -> 
	  List.iter (Logics.add (Profile.of_logictype ty) loc ac) lp;
	  TLogic(loc,ext,lp,ty)::acc
      | Axiom(loc,name,f) -> 
	  let f,_ = type_form Env.empty f in 
	  let f = Triggers.make true f loc in
	  TAxiom(loc,name,f)::acc
      | Goal(loc,n,f) -> 
	  (*let f = move_up f in*)
	  let env , axioms , goal = 
	    intro_hypothesis Env.empty 
	      (not (!smtfile or !satmode)) f in
	  let axioms =
	    List.fold_left
	      (fun acc f ->
		 let f,_ = type_form env f in
		 let f = Triggers.make true f loc in
		   TAxiom(loc,fresh_axiom_name(),f)::acc) acc axioms
	  in
	  let goal,_ = type_form env goal in
	  let goal = Triggers.make true goal loc in
	  TGoal(loc,n,goal)::axioms
      | Predicate_def(loc,n,l,e) 
      | Function_def(loc,n,l,_,e) ->
	  check_duplicate_params l;
	  let ty = 
	    let l = List.map (fun (_,_,x) -> x) l in
	    match d with
	      Function_def(_,_,_,t,_) -> PFunction(l,t) 
	    | _ -> PPredicate l 
	  in
	  let l = List.map (fun (_,x,t) -> (x,t)) l in
	  Logics.add (Profile.of_logictype ty) loc false n; (* TO DO *)
	  let lvar = List.map (fun (x,_) -> {pp_desc=PPvar x;pp_loc=loc}) l in
	  let p = {pp_desc=PPapp(n,lvar) ; pp_loc=loc } in
	  let infix = match d with Function_def _ -> PPeq | _ -> PPiff in
	  let f = { pp_desc = PPinfix(p,infix,e) ; pp_loc = loc } in
	  (* le trigger [[p]] ne permet pas de replier la definition *)
	  let f = make_pred loc [[p]] f l in
	  let f,_ = type_form Env.empty f in
	  let f = Triggers.make false f loc in
	  (match d with 
	     | Function_def(_,_,_,t,_) -> TFunction_def(loc,n,l,t,f)::acc
	     | _ ->  TPredicate_def(loc,n,l,f)::acc)
      | TypeDecl(loc,ext,ls,s) -> 
	  Types.add ls s loc;
	  TTypeDecl(loc,ext,ls,s)::acc
  with Warning(e,loc) -> 
    Loc.report loc; printf "Warning: %a@." report e;
    TWarning(loc)::acc

let split_file l = 
  let acc, ret = 
    List.fold_left
      (fun (acc,ret) x -> 
	 match x with 
	     Goal _ -> acc, (x::acc)::ret
	   | _ -> x::acc, ret) ([],[]) l
  in 
  let r = if acc=[] then ret else acc::ret in
  List.rev_map List.rev r

let file f = 
  List.rev 
    (List.fold_left 
       (fun acc l ->
	  Logics.clear();
	  Types.clear();
	  (List.rev (List.fold_left type_decl [] l))::acc) [] (split_file f))

let make_cnf l = 
  Decl.clear ();
  Logics.clear();
  Types.clear();
  List.iter
    (fun (d,b) -> match d with
	 TAxiom(loc,name,f) -> Decl.push_assume f name loc b
       | TGoal(loc,n,f) -> Decl.push_query n f loc
       | TPredicate_def(loc,n,[],f) -> Decl.push_assume f n loc b
       | TPredicate_def(loc,n,_,f) -> Decl.push_preddef f n loc b
       | TFunction_def(loc,n,_,_,f) -> Decl.push_assume f n loc b
       | _ -> ()) l;
  Decl.queue
    
