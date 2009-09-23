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

type 'a abstract

module type ALIEN = sig
  type r
  val make : Term.t -> r
  val type_infos : r -> Ty.t
  val extract : r -> (r abstract) option
  val embed : r abstract -> r
  val subst : r -> r -> r -> r
  val leaves : r -> r list
  val compare : r -> r -> int
  val print : Format.formatter -> r -> unit
end

module Make 
  (X : ALIEN) : Sig.THEORY with type r = X.r and type t = X.r abstract


