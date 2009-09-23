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

type loc = Lexing.position * Lexing.position

type constant =
  | ConstBitv of string
  | ConstInt of string
  | ConstReal of string
  | ConstNum of Num.num
  | ConstUnit

type pp_infix = 
  PPand | PPor | PPimplies | PPiff |
  PPlt | PPle | PPgt | PPge | PPeq | PPneq |
  PPadd | PPsub | PPmul | PPdiv | PPmod | PPat

type pp_prefix = 
  PPneg | PPnot 

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTbitv of int
  | PPTvarid of string * loc
  | PPTexternal of ppure_type list * string * loc

type lexpr = 
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of string
  | PPapp of string * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of string list* ppure_type * lexpr list list * lexpr
  | PPexists of string * ppure_type * lexpr
  | PPnamed of string * lexpr
  | PPlet of string * lexpr * lexpr

(* Declarations. *)

type external_ = bool

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type is_ac = Symbols.is_ac

type decl = 
  | Axiom of loc * string * lexpr
  | Goal of loc * string * lexpr
  | Logic of loc * is_ac * external_ * string list * plogic_type
  | Predicate_def of loc * string * (loc * string * ppure_type) list * lexpr
  | Function_def 
      of loc * string * (loc * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of loc * external_ * string list * string

type file = decl list

(*** typed ast *)

type tconstant =
  | Tint of string
  | Treal of string
  | Tnum of Num.num
  | Tbitv of string
  | Tunit

type tterm = 
    { tt_ty : Ty.t; tt_desc : tt_desc }
and tt_desc = 
  | TTtrue
  | TTfalse
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTapp of Symbols.t * tterm list
  | TTinfix of tterm * Symbols.t * tterm

type tatom = 
  | TAtrue
  | TAfalse
  | TAeq of tterm list
  | TAneq of tterm list
  | TAle of tterm list
  | TAlt of tterm list
  | TApred of tterm
  | TAbuilt of Hstring.t * tterm list

type oplogic = OPand |OPor | OPimp | OPnot | OPif of tterm | OPiff 

type quant_form = {       
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;

  qf_upvars : (Symbols.t * Ty.t) list ;

  qf_triggers : tterm list list ;
  qf_form : tform
}

and tform =
  | TFatom of tatom
  | TFop of oplogic * tform list
  | TFforall of quant_form
  | TFexists of quant_form
  | TFlet of (Symbols.t * Ty.t) list * Symbols.t * tterm * tform


type typed_decl = 
  | TAxiom of loc * string * tform
  | TGoal of loc * string * tform
  | TLogic of loc * external_ * string list * plogic_type
  | TPredicate_def of loc * string * (string * ppure_type) list * tform
  | TFunction_def 
      of loc * string * (string * ppure_type) list * ppure_type * tform
  | TTypeDecl of loc * external_ * string list * string
  | TWarning of loc
