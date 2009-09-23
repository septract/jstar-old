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

type error 

exception Error of error * Why_ptree.loc

type tdecl = 
  | Assume of Formula.t * Why_ptree.loc * bool
  | PredDef of Formula.t * Why_ptree.loc
  | Query of string * Formula.t * Literal.t list * Why_ptree.loc

val make_cnf : (Why_ptree.typed_decl * bool) list -> tdecl Queue.t

val file : Why_ptree.file -> Why_ptree.typed_decl list list

val report : Format.formatter -> error -> unit


