(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(*
 * ddino's implementation of control flow graph. 
 * This implementation is an adaptation of my implementation of the iterprocedural cfg for sil.
 *)


open Jparsetree
(*open Jimple_global_types *)
open Global_types
open Pprinter_core
open Pprinter 
open Support_symex

let debug =true

let cfg_debug () = false
(* special function for which the code does not exist. 
   They are mapped in a dummy node and skipped *)
(*let special_functions = ref [] *)


(* ============== START of functions for stmts ============== *)


let stmt_create_base _ = 
  Methdec_core.stmt_create (Nop_stmt_core)  [] [] 

let stmt_create_default pred_stmts succ_stmts = 
 Methdec_core.stmt_create (Nop_stmt_core) pred_stmts succ_stmts


let rec forallStmts (todo) (md : methdec) = 
    List.iter todo md.bstmts


(* ============== END of functions for stmts ============== *)





(* ============== START of ADT node and method_cfg_info ============== *)






(* =============== END of ADT node and method_cfg_info =============== *)


(* =============== START of icfg_build_intra_cfg =============== *)


(* Fill in the CFG info for a stmt *)
let cfgStmt (s: stmt_core) (next:stmt_core option) (prog: stmt_core list) =
  if s.succs <> [] then begin
    Printf.printf "CFG must be cleared before being computed!";
    assert false
  end;
  let addSucc (n: stmt_core) =
    if not (List.memq n s.succs) then
      let _ = if cfg_debug() then Printf.printf "\n Adding %i as successor of %i" n.sid s.sid in
      s.succs <- n::s.succs;
    if not (List.memq s n.preds) then
      let _ = if cfg_debug() then Printf.printf "  Adding %i as predecessor of %i \n" s.sid n.sid in
      n.preds <- s::n.preds in
  let addOptionSucc (n: stmt_core option) =
    match n with
      | None -> ()
      | Some n' -> addSucc n' in
  let find_label_stmt l=  
    try List.find (fun s' -> match s'.skind with 
    |  Label_stmt_core l' -> l=l'
    | _ -> false
	  ) prog
    with Not_found -> assert false
  in
  match s.skind with
   | Nop_stmt_core ->  addOptionSucc next
   | Label_stmt_core l -> addOptionSucc next  
   | Assignment_core (_,_,_) -> addOptionSucc next
   | If_stmt_core(_,l) -> 
       addSucc (find_label_stmt l);
       addOptionSucc next
   | Goto_stmt_core l -> addSucc (find_label_stmt l)
   | Throw_stmt_core imm -> () (* for the moment it goes to the end. Probably there should be a node for exceptions to denote abnormal termination. *)

let rec cfgStmts (ss: stmt_core list) (prog : stmt_core list) =
  match ss with
    | [] -> ()
    | [s] -> cfgStmt s None prog
    | hd::hd2::tl ->
	cfgStmt hd (Some hd2) prog;
	cfgStmts (hd2::tl) prog 











(* ================== START of Print interprocedural cfgs in dotty format  ================== *)
(* Print control flow graph (in dot form) for fundec to channel. 
   You have to compute an interprocedural cfg first *)


let d_cfgedge chan src dest =
  Printf.fprintf chan "%i -> %i" src.sid dest.sid

let d_cfgnode chan (s : stmt_core) =
  Printf.fprintf chan "%i [label=\"%i: %s\"]\n\t" s.sid s.sid (statement_core2str s.skind);
  List.iter (fun suc ->(d_cfgedge chan s suc); Printf.fprintf chan "\n\t") s.succs  

(** print control flow graph (in dot form) for methdec to channel *)
(* ddino: I think it can be simplified if we print everything in terms of nodes instead of stmts *)
(*
let print_cfg_channel (chan : out_channel) (md : methdec) =
  let pnode (s:stmt_core) =  d_cfgnode chan s
  in forallStmts pnode md;
  let minfo= mcfginfo_tbl_find (key_method md) in
  let sn= method_cfg_info_get_start_node minfo in
  Printf.fprintf chan "%i [label=\"%i: Method %s START\"]\n\t" (node_get_id sn) (node_get_id sn) (name2str md.name_m); 
  List.iter (fun suc ->(d_cfgedge chan sn.nd_stmt suc); Printf.fprintf chan "\n\t") sn.nd_stmt.succs;    
  let en= method_cfg_info_get_exit_node minfo in
  Printf.fprintf chan "%i [label=\"%i: Method %s EXIT\"]\n\t" (node_get_id en) (node_get_id en) (name2str md.name_m); 
  List.iter (fun suc ->(d_cfgedge chan en.nd_stmt suc); Printf.fprintf chan "\n\t") en.nd_stmt.succs    
   

(** Print control flow graph (in dot form) for fundec to file *)
let print_cfg_filename (filename : string) (md : methdec) =
  let chan = open_out filename in
    begin
      print_cfg_channel chan md;
      close_out chan;
    end

 

let print_icfg_dotty mdl =
  if cfg_debug () then ignore (Printf.printf "\n\nPrinting iCFG as dot file...");
  let chan = open_out (!file ^ ".icfg.dot") in
  ignore (Printf.fprintf chan "digraph iCFG {\n");
  List.iter (print_cfg_channel chan) mdl;
  ignore(Printf.fprintf chan  "}\n");
  close_out chan;
  if cfg_debug() then ignore (Printf.printf "\n\n Printing dot file done!")
*)
(* ================== END of Printing dotty files ================== *)




(* Call with non-empty statement list *)
let stmts_to_cfg stmts =
  cfgStmts stmts stmts
