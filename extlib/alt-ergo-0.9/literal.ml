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

open Hashcons

type view = 
    Eq of Term.t * Term.t 
  | Neq of Term.t * Term.t 
  | Builtin of bool * Hstring.t * Term.t list

type t = view hash_consed

module SS = Symbols.Set
	     
module H = 
  Make 
    (struct 
       type t=view 
	   
       let equal a1 a2 = 
	 match a1,a2 with
	     Eq(t1,t2) , Eq(u1,u2) 
	   | Neq(t1,t2) , Neq(u1,u2) -> Term.equal t1 u1 && Term.equal t2 u2
	   | Builtin(b1,n1,l1) , Builtin(b2,n2,l2) -> 
	       (try b1=b2 && 
		   Hstring.equal n1 n2 && List.for_all2 Term.equal l1 l2
		with Invalid_argument _ -> false)
	   | _ -> false
	     
       let hash a = match a with
	   Eq(t1,t2) | Neq(t1,t2) -> 
	     let k = match a with  Eq _ -> 1 | Neq _-> 3 | _ -> assert false in
	     abs ((k*19 + Term.hash t1)*19+Term.hash t2)
	 | Builtin(b,n,l) -> 
	     let x = if b then 1 else 0 in
	     List.fold_left 
	       (fun acc t-> acc*19 + Term.hash t)(Hstring.hash n+x) l
     end)
    
let tbl = H.create 100007
  
let make t = H.hashcons tbl t

let mk_pred t = make (Eq(t,Term.vrai))

let vrai = mk_pred Term.vrai
let faux = mk_pred Term.faux
  
let view a = a.node
  
let compare a1 a2 = Pervasives.compare a1.tag a2.tag
  
let equal a1 a2 = a1.tag = a2.tag
  
let hash a1 = a1.tag

let apply_subst subst a = 
  let f = Term.apply_subst subst in
  let a = match view a with
      Eq(t1,t2) -> Eq(f t1,f t2)
    | Neq(t1,t2) -> Neq(f t1,f t2)
    | Builtin(b,n,l) -> Builtin(b,n,List.map f l)
  in
  H.hashcons tbl a

let neg a = 
  let va = match view a with
    | Eq(t1,t2) when Term.equal t2 Term.faux -> Eq(t1,Term.vrai)
    | Eq(t1,t2) when Term.equal t2 Term.vrai -> Eq(t1,Term.faux)
    | Eq(t1,t2) -> Neq(t1,t2)
    | Neq(t1,t2) -> Eq(t1,t2)
    | Builtin(b,n,l) -> Builtin(not b,n,l)
  in 
  H.hashcons tbl va

let terms_of a = 
  let l = 
    match view a with Eq(t1,t2) | Neq(t1,t2) -> [t1;t2] | Builtin(_,_,l) -> l in
  List.fold_left Term.subterms  Term.Set.empty l

let is_var = function Symbols.Var _ -> true | _ -> false

let vars_of a = 
  Term.Set.fold (fun t -> SS.union (Term.vars_of t)) (terms_of a) SS.empty
        
let rec print fmt a = 
  match view a with
      Eq(t1,t2) -> 
	Format.fprintf fmt "%a=%a" Term.print t1 Term.print t2
    | Neq(t1,t2) -> 
	Format.fprintf fmt "%a<>%a" Term.print t1 Term.print t2
    | Builtin(true,n,l) ->
	Format.fprintf fmt "%s(%a)" (Hstring.view n) Term.print_list l
    | Builtin(false,n,l) ->
	Format.fprintf fmt "~%s(%a)" (Hstring.view n) Term.print_list l
and print_list fmt l = 
  List.iter (print fmt) l

module SetEq = Set.Make
  (struct 
     type t' = t * Term.t * Term.t
     type t = t'
     let compare (a1,_,_) (a2,_,_) = compare a1 a2
   end)
module Set = Set.Make(struct type t' = t type t=t' let compare=compare end)
module Map = Map.Make(struct type t' = t type t=t' let compare=compare end)
