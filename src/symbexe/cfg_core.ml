(********************************************************
   This file is part of jStar 
	src/symbexe/cfg_core.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2009,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)



open Pprinter_core
open Methdec_core

let cfg_debug () = false


(* Call with non-empty statement list *)
let stmts_to_cfg stmts =
  (* Fill in the CFG info for a stmt
     s  is the statement being filled in. 
     next is the next statment in program order.
     prog is the whole program. (This is required to lookup labels for jumps) *)
  let cfgStmt (s: stmt_core) (next:stmt_core option) (prog: stmt_core list) =
    if s.succs <> [] then begin
      Printf.printf "CFG must be cleared before being computed!";
      assert false
    end;
    (* Code to set the successor and predecessor of a node, and its successor. *)
    let addSucc (n: stmt_core) =
      assert (not (List.memq n s.succs));
      assert (not (List.memq s n.preds));
      if cfg_debug() then Printf.printf "\nAdding %i in %i.succ, and %i in %i.preds\n" n.sid s.sid s.sid n.sid;
      n.preds <- s::n.preds;
      s.succs <- n::s.succs in
    let addOptionSucc (n: stmt_core option) =
      match n with
      | None -> ()
      | Some n' -> addSucc n' in
    let find_label_stmt l=  
      try List.find 
	  (fun s' -> match s'.skind with 
	  |  Label_stmt_core l' -> l=l'
	  | _ -> false) 
	  prog
      with Not_found ->
	Printf.printf "Undefined label %s\n" l;
	assert false
    in
    match s.skind with
    | End -> ()
    | Nop_stmt_core ->  addOptionSucc next
    | Label_stmt_core l -> addOptionSucc next  
    | Assignment_core (_,_,_) -> addOptionSucc next
    | Goto_stmt_core ls -> List.iter (fun l -> addSucc (find_label_stmt l)) ls
    | Throw_stmt_core imm -> () (* for the moment it goes to the end. Probably there should be a node for exceptions to denote abnormal termination. *) in
  (* Fill in cfg for a list of statements. *)
  let rec cfgStmts (ss: stmt_core list) (prog : stmt_core list) =
  match ss with
    | [] -> ()
    | [s] -> cfgStmt s None prog
    | hd::hd2::tl ->
	cfgStmt hd (Some hd2) prog;
	cfgStmts (hd2::tl) prog in
  cfgStmts stmts stmts


let escape_for_dot_label s =
  Str.global_replace (Str.regexp "\\\\n") "\\l" (String.escaped s)

(* stmtsname is a list of programs and names, such that each program's
   cfg is printed in a subgraph with its name.*)
let print_icfg_dotty (stmtsname : (stmt_core list * string) list) (filename : string) : unit =
  (* Print an edge between to stmts *)
  let d_cfgedge chan src dest =
    Printf.fprintf chan "\t\t%i -> %i\n" src.sid dest.sid in
  (* Print a node and edges to its successors *)
  let d_cfgnode chan (s : stmt_core) =
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      s.sid 
      s.sid 
      (escape_for_dot_label (Debug.toString pp_stmt_core s.skind));
    List.iter (d_cfgedge chan s) s.succs  in

  if cfg_debug () then ignore (Printf.printf "\n\nPrinting iCFG as dot file...");
  let chan = open_out (filename ^ ".icfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  List.iter 
    (fun (stmts,name) -> 
      stmts_to_cfg stmts;
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (escape_for_dot_label name);
      List.iter (d_cfgnode chan) stmts;
      Printf.fprintf chan  "\t}\n";
    ) 
    stmtsname;
  Printf.fprintf chan  "}\n";
  close_out chan;
  if cfg_debug() then ignore (Printf.printf "\n\n Printing dot file done!")

(* ================== END of Printing dotty files ================== *)




