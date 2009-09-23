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


(*----------------------------------------------------------------------------
  - Decision procedure like types and functions 
  - To be used by Combine
  ---------------------------------------------------------------------------*)

module type SMake = sig 
  type r
  type t = r Sig.ac
  val print : Format.formatter -> t -> unit
  val subst : r -> r -> t -> r 
  val compare : t -> t -> int
  val is_mine_hs :Term.t -> bool
  val make : Term.t -> r
  val type_infos : t -> Ty.t
  val leaves : t -> r list
end
  
module Make (X : Sig.X) : SMake with type r = X.r
