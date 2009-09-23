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

(* Persistent and incremental congruence-closure modulo X data structure. 

   This module implements the CC(X) algorithm.

*)

module type S = sig
  type t

  val empty : unit -> t
  val add : Literal.t -> t -> t
  val assume : Literal.t -> Explanation.t -> t -> t
  val query : Literal.t -> t -> bool
  val class_of : t -> Term.t -> Term.t list
  val explain : Literal.t -> t -> Explanation.t
end

module Make (X:Sig.X) : S
