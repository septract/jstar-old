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

type view = 
    Eq of Term.t * Term.t 
  | Neq of Term.t * Term.t 
  | Builtin of bool * Hstring.t * Term.t list

type t

val make : view -> t
val mk_pred : Term.t -> t

val vrai : t
val faux : t 

val view : t -> view
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

val neg : t -> t
val apply_subst : Term.subst -> t -> t

val terms_of : t -> Term.Set.t
val vars_of : t -> Symbols.Set.t

val print : Format.formatter -> t -> unit
val print_list : Format.formatter -> t list-> unit

module SetEq : Set.S with type elt = t * Term.t * Term.t
module Map : Map.S with type key = t
module Set : Set.S with type elt = t

