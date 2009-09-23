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

module type COEF = sig
  type t
  val of_int : string -> t
  val zero : t
  val one : t 
  val minusone : t 
  val plus : t -> t -> t
  val minus : t -> t -> t
  val mult : t -> t -> t
  val inverse : t -> t

  val compare : t -> t -> int

  val print : Format.formatter -> t -> unit

end

module type S = sig

  type coef
  module XM : Map.S
  module X : Sig.COMBINATOR

  type view = coef XM.t * coef
  type t

  val is_num : t -> bool
  
  val make : Term.t -> (t,X.r) Sig.mine
  val embedding : X.r -> t

  val leaves : t -> XM.key list

  val view : t -> view

  val compare : t -> t -> int

  val mult : coef -> t -> t
  val add : t -> t -> t
  val add_one : t -> t

  val choose : t -> X.r * coef
  val subst : X.r -> t -> t -> (t,X.r) Sig.mine
  val canon : t -> (X.r -> t) -> t 
  val solve : t -> t -> (X.r * (t,X.r) Sig.mine) list

  val print : Format.formatter -> t -> unit

end

module Make (C:COEF)(X:Sig.COMBINATOR) : S 
  with type coef=C.t and type XM.key = X.r and module X = X
	
