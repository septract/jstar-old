(********************************************************
   This file is part of jStar 
	src/symbexe_syntax/methdec_core.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)


(* Manage methdec infos for a file *) 

open Spec

type core_statement = 
  | Nop_stmt_core
  | Label_stmt_core of  string 
  | Assignment_core of Vars.var list * spec * Psyntax.args list
  | Goto_stmt_core of string list  
  | Throw_stmt_core of Psyntax.args
  | End

type symb_question = 
  | Specification of string * spec * core_statement list 
  
type symb_test = 
  | SpecTest of string * spec * core_statement list * bool  

