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

val fmt : Format.formatter
val file : string ref

val parse_only : bool
val type_only : bool
val stopb : int
val notriggers : bool
val debug : bool
val debug_cc : bool
val debug_use : bool
val debug_uf : bool
val debug_fm : bool
val debug_bitv : bool
val debug_ac : bool
val debug_sat : bool
val debug_sat_simple : bool
val debug_typing : bool
val debug_constr : bool
val debug_pairs : bool
val verbose : bool
val debug_dispatch : bool
val tracefile :string
val smtfile :bool ref
val satmode : bool ref
val bjmode : bool
val glouton : bool
val triggers_var : bool
val redondance : int
val astuce : bool
val select : int
val cin : in_channel
