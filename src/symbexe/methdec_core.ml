(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(* Manage methdec infos for a file *) 

open Jparsetree
open Specification

type core_statement = 
  | Nop_stmt_core
  | Label_stmt_core of  string 
  | Assignment_core of Vars.var list * spec * Pterm.args list
  | Goto_stmt_core of string list  
  | Throw_stmt_core of Pterm.args



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


