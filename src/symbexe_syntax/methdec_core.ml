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


type stmt_core = { 
  (*labels: labels; *)
  mutable skind: core_statement;
  mutable sid: int;  (* this is filled when the cfg is done *)
  mutable succs: stmt_core list; (* this is filled when the cfg is done *)
  mutable preds: stmt_core list  (* this is filled when the cfg is done *)
 }



let num_stmts = ref 0 


let stmt_create 
    (skind: core_statement)  
    (pred_stmts: stmt_core list)  
    (succ_stmts: stmt_core list) 
    : stmt_core = 
incr num_stmts;
  { skind = skind;
    sid = !num_stmts; 
    succs = succ_stmts;
    preds = pred_stmts }


