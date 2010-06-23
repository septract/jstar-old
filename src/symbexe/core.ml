(********************************************************
   This file is part of jStar 
	src/symbexe/core.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

(** The `core' language. See also cfg_core.ml and pprinter_core.ml. *)

type core_statement = 
  | Nop_stmt_core
  | Label_stmt_core of  string 
  | Assignment_core of Vars.var list * Spec.spec * Psyntax.args list
  | Goto_stmt_core of string list  
  | Throw_stmt_core of Psyntax.args
  | End

