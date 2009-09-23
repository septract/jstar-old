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

type ('a,'b) mine = Yes of 'a | No of 'b

type 'a ac = Hstring.t * 'a list

module type RELATION = sig
  type t
  type elt

  val empty : unit -> t
  val assume : 
    t -> Literal.Set.t -> (Term.t -> elt) -> (Term.t -> Term.t list)  -> 
    t * Literal.SetEq.t
  val query : 
    Literal.t -> (Term.t -> elt) -> (Term.t -> Term.t list)  -> t -> bool 
end

module type THEORY = sig

  (**Type of terms of the theory*)
  type t
  (**Type of representants of terms of the theory*)
  type r
  (** Name of the theory*)
  val name : string
  (** return true if the atom is owned by the theory*)
  val is_mine_a : Literal.t -> bool
  (** return true if the head symbol is owned by the theory*)
  val is_mine_hs : Term.t -> bool
  (** return true if the type is owned by the theory*)
  val is_mine_type : t -> bool

  (** Give a normal form of a term of the theory*)
  val normal_form : Literal.t -> Literal.t
  (** Give a representant of a term of the theory*)
  val make : Term.t -> r
  val type_infos : t -> Ty.t
  val embedding : r -> t

  (** Give the leaves of a term of the theory *)
  val leaves : r -> r list
  val subst : r -> r -> t -> r

  val compare : t -> t -> int
  (** solve r1 r2, solve the equality r1=r2 and return the substitution *)

  val solve : r -> r ->  (r * r) list

  val print : Format.formatter -> t -> unit
  module R : RELATION with type elt = t
end

module type COMBINATOR = sig
  type r
  type th

  val extract : r -> th
  val make : Term.t -> r
  val type_infos : r -> Ty.t
  val compare : r -> r -> int
  val leaves : r -> r list
  val subst : r -> r -> r -> r
  val solve : r -> r ->  (r * r) list
  val empty_embedding : Term.t -> r
  val normal_form : Literal.t -> Literal.t
  val print : Format.formatter -> r -> unit
  module R : RELATION with type elt = r

end

module type X = sig
  type r

  val make : Term.t -> r
  val type_infos : r -> Ty.t
  val compare : r -> r -> int
  val leaves : r -> r list
  val subst : r -> r -> r -> r
  val solve : r -> r ->  (r * r) list
  val term_embed : Term.t -> r
  val exist_embed : r -> r
  val ac_embed : r ac -> r
  val ac_extract : r -> (r ac) option
  val is_empty   : r -> bool
  val normal_form : Literal.t -> Literal.t
  val print : Format.formatter -> r -> unit
  module R : RELATION with type elt = r
end


module type EXPLANATION = sig
  type t = Formula.Set.t option

  val union : t -> t-> t
end
