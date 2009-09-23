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

type rat

module type ALIEN = sig
  type r
  val compare : r -> r -> int
  val make : Term.t -> r
  val subst : r -> r -> r -> r
  val leaves : r -> r list
  val print : Format.formatter -> r -> unit
  val term_embed : Term.t -> r
end

module type T = sig 
  type r 
  module M : Map.S with type key = r 
  module S : Set.S with type elt = r 
  type t = rat M.t * rat

  val compare : t -> t -> int
  val make : Term.t -> r
  val subst : r -> r -> r -> r
  val leaves : r -> r list
  val term_embed : Term.t -> r
  val print : Format.formatter -> r -> unit
end 

module Type (A:ALIEN) : T with type r = A.r 

module type TARITH = sig
  include T
  val extract : r -> t option
  val embed : t -> r
end

module Make (X : TARITH) : Sig.THEORY with type r = X.r and type t = X.t
