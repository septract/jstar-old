/**************************************************************************/
/*                                                                        */
/*     The Alt-ergo theorem prover                                        */
/*     Copyright (C) 2006-2009                                            */
/*                                                                        */
/*     Sylvain Conchon                                                    */
/*     Evelyne Contejean                                                  */
/*     Stephane Lescuyer                                                  */
/*     Mohamed Iguernelala                                                */
/*                                                                        */
/*     CNRS - INRIA - Universite Paris Sud                                */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/

/*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 */

/* from http://www.lysator.liu.se/c/ANSI-C-grammar-y.html */

%{

  open Why_ptree
  open Parsing

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (loc ()) d
  let mk_pp_i i d = mk_ppl (loc_i i) d
		    
  let infix_ppl loc a i b = mk_ppl loc (PPinfix (a, i, b))
  let infix_pp a i b = infix_ppl (loc ()) a i b

  let prefix_ppl loc p a = mk_ppl loc (PPprefix (p, a))
  let prefix_pp p a = prefix_ppl (loc ()) p a

  let check_binary_mode s = 
    String.iter (fun x-> if x<>'0' && x<>'1' then raise Parsing.Parse_error) s;
    s

%}

/* Tokens */ 

%token <string> IDENT
%token <string> INTEGER
%token <string> FLOAT
%token <Num.num> NUM
%token <string> STRING
%token AND ARRAY ARROW AS AT AXIOM 
%token BAR HAT
%token BOOL COLON COMMA DOT ELSE EOF EQUAL
%token EXISTS EXTERNAL FALSE FORALL FUNCTION GE GOAL GT
%token IF INT BITV
%token LE  LEFTPAR LEFTSQ LEFTBR LOGIC LOGIC_AC LRARROW LT MINUS 
%token LNOT NOT NOTEQ OR PARAMETER PERCENT PLUS PREDICATE PROP 
%token QUOTE REAL
%token RIGHTPAR RIGHTSQ RIGHTBR
%token SEMICOLON SLASH 
%token THEN TIMES TRUE TYPE UNIT VOID

/* Precedences */

%nonassoc prec_recfun
%nonassoc prec_fun
%left prec_simple

%left COLON 

%left prec_letrec

%right SEMICOLON

%left prec_no_else
%left ELSE

%right prec_named
%right prec_forall prec_exists
%right ARROW LRARROW
%right OR
%right AND 
%right NOT LNOT
%right prec_if
%left prec_relation EQUAL NOTEQ LT LE GT GE
%left PLUS MINUS
%left TIMES SLASH PERCENT AT
%left HAT
%right uminus
%left prec_app
%left prec_ident
%left LEFTSQ

/* Entry points */

%type <Why_ptree.lexpr> lexpr
%start lexpr
%type <Why_ptree.file> file
%start file
%%

file:
| list1_decl EOF 
   { $1 }
| EOF 
   { [] }
;

list1_decl:
| decl 
   { [$1] }
| decl list1_decl 
   { $1 :: $2 }
;

decl:
| AXIOM ident COLON lexpr
   { Axiom (loc (), $2, $4) }
| GOAL ident COLON lexpr
   { Goal (loc (), $2, $4) }
| PREDICATE ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR EQUAL lexpr
   { Predicate_def (loc (), $2, $4, $7) }
| FUNCTION ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR COLON 
  primitive_type EQUAL lexpr
   { Function_def (loc (), $2, $4, $7, $9) }
| external_ TYPE ident
   { TypeDecl (loc_i 3, $1, [], $3) }
| external_ TYPE type_var ident
   { TypeDecl (loc_ij 2 3, $1, [$3], $4) }
| external_ TYPE LEFTPAR list1_type_var_sep_comma RIGHTPAR ident
   { TypeDecl (loc_ij 3 6, $1, $4, $6) }
| external_ LOGIC list1_ident_sep_comma COLON logic_type
   { Logic (loc (), false, $1, $3, $5) }
| external_ LOGIC_AC list1_ident_sep_comma COLON logic_type
   { Logic (loc (), true, $1, $3, $5) }
;

primitive_type:
| INT 
   { PPTint }
| BOOL 
   { PPTbool }
| REAL 
   { PPTreal }
| UNIT 
   { PPTunit }
| BITV LEFTSQ INTEGER RIGHTSQ
   { PPTbitv(int_of_string $3) }
| type_var 
   { PPTvarid ($1, loc ()) }
| ident 
   { PPTexternal ([], $1, loc ()) }
| primitive_type ident
   { PPTexternal ([$1], $2, loc_i 2) }
| LEFTPAR primitive_type COMMA list1_primitive_type_sep_comma RIGHTPAR ident
   { PPTexternal ($2 :: $4, $6, loc_i 6) }
;

logic_type:
| list0_primitive_type_sep_comma ARROW PROP
   { PPredicate $1 }
| PROP
   { PPredicate [] }
| list0_primitive_type_sep_comma ARROW primitive_type
   { PFunction ($1, $3) }
| primitive_type
   { PFunction ([], $1) }
;

list0_primitive_type_sep_comma:
| /* epsilon */                  { [] }
| list1_primitive_type_sep_comma { $1 }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

list0_logic_binder_sep_comma:
| /* epsilon */                { [] }
| list1_logic_binder_sep_comma { $1 }
;

list1_logic_binder_sep_comma:
| logic_binder                                    { [$1] }
| logic_binder COMMA list1_logic_binder_sep_comma { $1 :: $3 }
;

logic_binder:
| ident COLON primitive_type       
    { (loc_i 1, $1, $3) }
| ident COLON primitive_type ARRAY 
    { (loc_i 1, $1, PPTexternal ([$3], "farray", loc_i 3)) }
;

external_:
| /* epsilon */ { false }
| EXTERNAL      { true  }
;

lexpr:
| LEFTSQ INTEGER RIGHTSQ
    { mk_pp (PPconst (ConstBitv (check_binary_mode $2))) }
| lexpr ARROW lexpr 
   { infix_pp $1 PPimplies $3 }
| lexpr LRARROW lexpr 
   { infix_pp $1 PPiff $3 }
| lexpr OR lexpr 
   { infix_pp $1 PPor $3 }
| lexpr AND lexpr 
   { infix_pp $1 PPand $3 }
| NOT lexpr 
   { prefix_pp PPnot $2 }
| lexpr relation lexpr %prec prec_relation
   { infix_pp $1 $2 $3 }
| lexpr PLUS lexpr
   { infix_pp $1 PPadd $3 }
| lexpr MINUS lexpr
   { infix_pp $1 PPsub $3 }
| lexpr TIMES lexpr
   { infix_pp $1 PPmul $3 }
| lexpr AT lexpr
   { infix_pp $1 PPat $3 }
| lexpr SLASH lexpr
   { infix_pp $1 PPdiv $3 }
| lexpr PERCENT lexpr
   { infix_pp $1 PPmod $3 }
| MINUS lexpr %prec uminus
   { prefix_pp PPneg $2 }
| lexpr HAT LEFTBR INTEGER COMMA INTEGER RIGHTBR
   { let i =  mk_pp (PPconst (ConstInt $4)) in
     let j =  mk_pp (PPconst (ConstInt $6)) in
     mk_pp (PPapp ("^",[$1; i ; j])) }
| ident
   { mk_pp (PPvar $1) }
| ident LEFTPAR list1_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPapp ($1, $3)) }
| ident LEFTSQ lexpr RIGHTSQ
   { mk_pp (PPapp ("access", [mk_pp_i 1 (PPvar $1); $3])) }
| IF lexpr THEN lexpr ELSE lexpr %prec prec_if 
   { mk_pp (PPif ($2, $4, $6)) }
| FORALL list1_ident_sep_comma COLON primitive_type triggers 
  DOT lexpr %prec prec_forall
   { mk_pp (PPforall ($2, $4, $5, $7)) }
| EXISTS ident COLON primitive_type DOT lexpr %prec prec_exists
   { mk_pp (PPexists ($2, $4, $6)) }
| INTEGER
   { mk_pp (PPconst (ConstInt $1)) }
| FLOAT
   { mk_pp (PPconst (ConstReal $1)) }
| NUM
   { mk_pp (PPconst (ConstNum $1)) }
| TRUE
   { mk_pp PPtrue }
| FALSE
   { mk_pp PPfalse }    
| VOID
   { mk_pp (PPconst ConstUnit) }
| LEFTPAR lexpr RIGHTPAR
   { $2 }
| ident_or_string COLON lexpr %prec prec_named
   { mk_pp (PPnamed ($1, $3)) }
;

triggers:
| /* epsilon */ { [] }
| LEFTSQ list1_trigger_sep_bar RIGHTSQ { $2 }
;

list1_trigger_sep_bar:
| trigger { [$1] }
| trigger BAR list1_trigger_sep_bar { $1 :: $3 }
;

trigger:
  list1_lexpr_sep_comma { $1 }
;

list1_lexpr_sep_comma:
| lexpr                             { [$1] }
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

relation:
| LT { PPlt }
| LE { PPle }
| GT { PPgt }
| GE { PPge }
| EQUAL { PPeq }
| NOTEQ { PPneq }
;

type_var:
| QUOTE ident { $2 }
;

list1_type_var_sep_comma:
| type_var                                { [$1] }
| type_var COMMA list1_type_var_sep_comma { $1 :: $3 }
;

ident:
| IDENT { $1 }
;

list1_ident_sep_comma:
| ident                             { [$1] }
| ident COMMA list1_ident_sep_comma { $1 :: $3 }
;

ident_or_string:
| IDENT  { $1 }
| STRING { $1 }
;
