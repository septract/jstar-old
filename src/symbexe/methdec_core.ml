(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(* Manage methdec infos for a file *) 

open Jparsetree
open Global_types 


let num_stmts = ref 0 


let stmt_create (skind: Global_types.core_statement)  
(pred_stmts: Global_types.stmt_core list)  
(succ_stmts: Global_types.stmt_core list) : Global_types.stmt_core = 
incr num_stmts;
  { skind = skind;
    sid = !num_stmts; 
    succs = succ_stmts;
    preds = pred_stmts }


