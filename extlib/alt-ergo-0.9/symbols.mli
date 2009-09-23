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

type binop = Plus | Minus | Mult | Div | Modulo | At
type is_ac = bool
type t = 
    Name of Hstring.t * is_ac
  | Int of Hstring.t
  | Rat of Hstring.t
  | Bitv of string
  | Binop of binop 
  | Var of Hstring.t

val name : ?ac:is_ac -> string -> t
val var : string -> t
val underscoring : t -> t
val int : string -> t
val rat : string -> t
val unit : t 

val shat : t

val is_ac : t -> bool

val plus : t
val minus : t
val mult : t
val div : t
val modulo : t
val at : t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val print : Format.formatter -> t -> unit

val dummy : t
val fresh : string -> t
  
module Map : Map.S with type key = t
module Set : Set.S with type elt = t

