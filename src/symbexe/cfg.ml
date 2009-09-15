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
open Pprinter
open Support_symex

let debug =true

let cfg_debug () = false
(* special function for which the code does not exist. 
   They are mapped in a dummy node and skipped *)
(*let special_functions = ref [] *)


(* ============== START of functions for stmts ============== *)


let stmt_create_base _ = 
  Methdec.stmt_create (Nop_stmt)  [] [] 

let stmt_create_default pred_stmts succ_stmts = 
 Methdec.stmt_create (Nop_stmt) pred_stmts succ_stmts


let rec forallStmts (todo) (md : methdec) = 
    List.iter todo md.bstmts;


(* ============== END of functions for stmts ============== *)





(* ============== START of ADT node and method_cfg_info ============== *)

type nodekind = Start_node | Exit_node | Call_node | Return_Site_node | Stmt_node


type node = {
(*  mutable nd_id:int; (* unique identifier for node *) *)
  mutable nd_kind : nodekind;
  nd_stmt : stmt;
  mutable nd_succs : node list;
  mutable nd_preds : node list;
  mutable nd_method : method_cfg_info option 
}
and method_cfg_info = {   
  pd_md : methdec; 
  pd_start_node : node; 
  pd_exit_node : node;
}

type id_node_hashtbl = (int, node) Hashtbl.t

let id_node_map : id_node_hashtbl = Hashtbl.create 1000

let i2s i = Printf.sprintf "%i" i

let id_node_map_add id node = 
  if cfg_debug() then Printf.printf "\n Adding node %i: %s in the table stmt.sid=%i\n" id (statement2str node.nd_stmt.skind) node.nd_stmt.sid;
  if cfg_debug() then Printf.printf "\n Successor nodes: %s" (String.concat ", " (List.map (fun node -> i2s node.nd_stmt.sid) node.nd_succs));
  Hashtbl.add id_node_map id node

let id_node_map_find key =
  try 
    Hashtbl.find id_node_map key
  with Not_found -> 
    let _ =Printf.printf "\n I cannot find node %i in the table \n" key in
    assert false

      

let node_to_sid node = node.nd_stmt.sid

let stmt_to_node stmt = id_node_map_find stmt.sid

let sid_to_node id = id_node_map_find id

let node_list : node list ref = ref []

let get_all_nodes _ = !node_list




let node_create kind stmt succ_nodes pred_nodes method_cfg_info_opt = 
  let node =
    { (* nd_id = stmt.sid;*)
      nd_kind = kind; 
      nd_stmt = stmt; 
      nd_succs = succ_nodes; 
      nd_preds = pred_nodes; 
      nd_method = method_cfg_info_opt } 
  in 
    node_list := node :: !node_list;
    id_node_map_add stmt.sid node;
    node

let node_create_base kind stmt =
  node_create kind stmt [] [] None

let node_get_succs node =
  node.nd_succs

let node_get_preds node =
  node.nd_preds

let node_get_kind node =
  node.nd_kind

let node_get_stmt node =
  node.nd_stmt

let node_set_method_cfg_info mdesc node =
  node.nd_method <- Some mdesc

let node_get_method_cfg_info node =
  let method_cfg_info = match node.nd_method with
    | None -> assert false
    | Some(method_cfg_info) -> method_cfg_info
  in method_cfg_info

let node_get_id node = node.nd_stmt.sid

let node_equal node1 node2 = (node_get_id node1) = (node_get_id node2) 

let node2str node = string_of_int (node_get_id node) 

let note_get_meth_dec node = 
  let i=node_get_method_cfg_info node in
  i.pd_md

let node_print node = 
  Printf.printf "%s" (node2str node)

let node_list_print nodes = 
  Printf.printf "[ %s ]" (list2str node2str nodes ",")  

type mcfginfo_tbl_t = (string, method_cfg_info) Hashtbl.t 

let mcfginfo_tbl : mcfginfo_tbl_t = Hashtbl.create 1000

let mcfginfo_tbl_add method_name method_cfg_info = 
  if cfg_debug() then Printf.printf "\n Adding method desc for %s" method_name;
  Hashtbl.add mcfginfo_tbl method_name method_cfg_info

let mcfginfo_tbl_find key =
  try
    Hashtbl.find mcfginfo_tbl key
  with Not_found -> 
    let _ =Printf.printf "\n I cannot find mdesc %s in the table \n" key in
    assert false



let print_list_stmts s lstmt =
  let l=List.map (fun s -> s.sid) lstmt in
  Printf.printf "\n   %s =[" s;
  List.iter (fun i -> Printf.printf "%i, " i ) l;
  Printf.printf " ]\n"

let print_node n =
  Printf.printf "\n Node statement sid=%i  skind=%s" n.nd_stmt.sid (statement2str n.nd_stmt.skind);
  print_list_stmts "Successors" n.nd_stmt.succs;
  print_list_stmts "Predecessors" n.nd_stmt.preds




let method_cfg_info_create md start_node exit_node  =
  { pd_md=md;  
    pd_start_node=start_node;
    pd_exit_node=exit_node;
}

   
let key_method md = 
  match md.params with 
  |Some pl ->(j_type2str md.ret_type)^"_"^(name2str md.name)^"_"^(list2str parameter2str pl "_")
  |None -> (j_type2str  md.ret_type) ^"_"^(name2str md.name)


let method_cfg_info_create_base md =
  let start_stmt = stmt_create_base () in
  let exit_stmt = stmt_create_base () in
  let start_node = node_create_base Start_node start_stmt in
  let exit_node = node_create_base Exit_node exit_stmt in
  let method_cfg_info = method_cfg_info_create md start_node exit_node in 
  node_set_method_cfg_info method_cfg_info start_node;
  node_set_method_cfg_info method_cfg_info exit_node;
  mcfginfo_tbl_add (key_method md) method_cfg_info;
  method_cfg_info


let method_cfg_info_to_method_name method_cfg_info =
  method_cfg_info.pd_md.name 

let method_name_to_method_cfg_info key =
  mcfginfo_tbl_find key

let method_cfg_info_get_methdec method_cfg_info =
  method_cfg_info.pd_md


let method_cfg_info_get_formals method_cfg_info =
  method_cfg_info.pd_md.params


let method_cfg_info_get_start_node method_cfg_info =
  method_cfg_info.pd_start_node

let method_cfg_info_get_exit_node method_cfg_info =
  method_cfg_info.pd_exit_node


(* =============== END of ADT node and method_cfg_info =============== *)


let icfg_create_method_cfg_infos (lmd: Jparsetree.methdec list) : unit = 
  if cfg_debug() then Printf.printf "\nCreating method_cfg_infos for all methods...";
  List.iter (fun m -> ignore(method_cfg_info_create_base m )) lmd;
  if cfg_debug() then Printf.printf "\nEND creation of method_cfg_infos for all methods..."; 
  ()


(* =============== START of icfg_build_intra_cfg =============== *)

let rec cfgStmts (mdesc: method_cfg_info) (ss: stmt list) 
    (next:stmt option) (break:stmt option) (cont:stmt option) =
  match ss with
    | [] -> ()
    | [s] -> cfgStmt mdesc s next break cont
    | hd::tl ->
	cfgStmt mdesc hd (Some (List.hd tl))  break cont;
	cfgStmts mdesc tl next break cont


and cfgBlock (mdesc: method_cfg_info) (bstmts: stmt list) 
    (next:stmt option) (break:stmt option) (cont:stmt option) = 
  cfgStmts mdesc bstmts next break cont 



(* Fill in the CFG info for a stmt
   Meaning of next, break, cont should be clear from earlier comment *)
and cfgStmt (minfo: method_cfg_info) (s: stmt) 
    (next:stmt option) (break:stmt option) (cont:stmt option) =
(*    incr num_stmts;
    s.sid <- !num_stmts;
*)
  if s.succs <> [] then begin
    Printf.printf "CFG must be cleared before being computed!";
    assert false
  end;
  let addSucc (n: stmt) =
    if not (List.memq n s.succs) then
      let _ = if cfg_debug() then Printf.printf "\n Adding %i as successor of %i" n.sid s.sid in
      s.succs <- n::s.succs;
    if not (List.memq s n.preds) then
      let _ = if cfg_debug() then Printf.printf "  Adding %i as predecessor of %i \n" s.sid n.sid in
      n.preds <- s::n.preds in
  let addOptionSucc (n: stmt option) =
    match n with
      | None -> ()
      | Some n' -> addSucc n' in
  let find_label_stmt l=
    let lstmt=minfo.pd_md.bstmts in
    try List.find (fun s' -> match s'.skind with 
		   |  Label_stmt l' -> l=l'
		   | _ -> false
		  ) lstmt
    with Not_found -> assert false
  in
  let get_list_labels case_stm_list =
    List.map (fun c -> match c with Case_stmt(_,l) -> l) case_stm_list
  in  
(*
  let addBlockSucc (b: block) = assert false
    match b.bstmts with
      |	[] -> addOptionSucc next
      | hd::_ -> addSucc hd in
*)
  let node = node_create_base (Stmt_node) s 
  in
  node_set_method_cfg_info minfo node; 
  match s.skind with
   | Label_stmt l -> addOptionSucc next  
   | Breakpoint_stmt -> addOptionSucc break
   | Entermonitor_stmt imm -> addOptionSucc next 
   | Exitmonitor_stmt imm -> addOptionSucc next 
   | Identity_no_type_stmt(n,id) -> addOptionSucc next 
   | Assign_stmt(v,e) -> addOptionSucc next
   | Goto_stmt l -> addSucc (find_label_stmt l)
   | If_stmt(_,l) -> 
       addSucc (find_label_stmt l);
       addOptionSucc next
   | Nop_stmt ->  addOptionSucc next
   | Identity_stmt (n,id,ty) -> addOptionSucc next 
   | Ret_stmt _ -> ()
   | Return_stmt _ -> ()
   | Invoke_stmt ie -> addOptionSucc next  
   | Throw_stmt imm -> () (* for the moment it goes to the end. Probably there should be a node for exceptions to denote abnormal termination. *)
   | Tableswitch_stmt (_, case_stm_list)   
   | Lookupswitch_stmt (_,case_stm_list) -> 
       let ll=get_list_labels case_stm_list in
       List.iter (fun l -> addSucc (find_label_stmt l)) ll       


(* compute the set of start stmts. *)
let compute_start_stmts md = 
  let start_stmts=List.filter (fun s -> s.preds = [])  md.bstmts in
    if debug then begin
      let start_statements=List.map (fun s -> s.skind) start_stmts in
      let ls=list2str statement2str start_statements "\n"in
      if cfg_debug() then Printf.printf "\n start_node=[ %s ]\n" ls
    end;
    start_stmts  


(* compute the set of exit stmts. *)
let compute_exit_stmts md = 
  let exit_stmts=List.filter (fun s -> s.succs = [])  md.bstmts in
    if debug then begin
      let exit_statements=List.map (fun s -> s.skind) exit_stmts in
      let ls=list2str statement2str exit_statements "\n"in
      if cfg_debug() then Printf.printf "\n exit_node=[ %s ]\n" ls
    end;
    exit_stmts  



let initialize_start_node method_cfg_info stmts =
  let start_stmt = method_cfg_info.pd_start_node.nd_stmt in
  let set_preds stmt = stmt.preds <- [start_stmt] 
  in  
    start_stmt.succs <- stmts;
    List.iter set_preds stmts


let initialize_exit_node method_cfg_info stmts = 
  let exit_stmt = method_cfg_info.pd_exit_node.nd_stmt in
  let set_succs stmt = stmt.succs <- [exit_stmt]
  in 
    exit_stmt.preds <- stmts;
    List.iter set_succs stmts
 


(* Compute a control flow graph for md.  Stmts in md have preds and succs
   filled in *)
let rec icfg_build_intra_cfg (md : methdec) : unit = 
  if cfg_debug() then Printf.printf "\nComputing intra CFG for %s..." (name2str md.name); 
  let method_cfg_info = mcfginfo_tbl_find  (key_method md) in
  let _ = cfgBlock method_cfg_info md.bstmts None None None in

  let start_stmts_of_md = compute_start_stmts md in
  let exit_stmts_of_md = compute_exit_stmts md 
  in initialize_start_node method_cfg_info start_stmts_of_md;
    initialize_exit_node method_cfg_info exit_stmts_of_md

(* =============== END of icfg_build_intra_cfg =============== *)




(* Creates a control flow graph for a function called svar *)
let create_undefined_method svar = assert false
(*let dummy_fd = { Cil.dummyFunDec with svar = svar } in
  let method_cfg_info = method_cfg_info_create_base dummy_fd in 
  let start_stmt = method_cfg_info.pd_start_node.nd_stmt in
  let exit_stmt = method_cfg_info.pd_exit_node.nd_stmt
  in 
     start_stmt.succs <- [exit_stmt];
     exit_stmt.preds <- [start_stmt];
     special_functions := svar.vname :: !special_functions;
     method_cfg_info
*)


let add_return_site_node stmt md = 
  let return_site_stmt = stmt_create_default [stmt] stmt.succs in
  let return_site_node = node_create_base Return_Site_node return_site_stmt in
  let _ = node_set_method_cfg_info md return_site_node in
  let node = stmt_to_node stmt in
  node.nd_kind <- Call_node;
  List.iter (fun p -> p.preds <- [return_site_stmt]) stmt.succs;
  stmt.succs <- [return_site_stmt]













(* =============== START of icfg_compute_node_edges =============== *)

let set_succs_of_node node =
  let stmt = node.nd_stmt in
  let succ_stmts = stmt.succs in
  let succ_nodes = List.map stmt_to_node succ_stmts
  in node.nd_succs <- succ_nodes

let set_preds_of_node node = 
  let stmt = node.nd_stmt in
  let pred_stmts = stmt.preds in
  let pred_nodes = List.map stmt_to_node pred_stmts
  in node.nd_preds <- pred_nodes 

let icfg_compute_node_edges _ =
  let fill_preds_succs node = 
    set_succs_of_node node;
    set_preds_of_node node 
  in List.iter fill_preds_succs !node_list

(* =============== END of icfg_compute_node_edges =============== *)




(* ================== START of functions about interprocedural CFG ================== *)

let clearCFGinfo (md : methdec) =
  let clear s =
    s.sid <- -1;
    s.succs <- [];
    s.preds <- []
  in
    forallStmts clear md

let clearFileCFG mdl =
  List.iter clearCFGinfo mdl





(* ================== END of functions about interprocedural CFG ================== *)





(* ================== START of Print interprocedural cfgs in dotty format  ================== *)
(* Print control flow graph (in dot form) for fundec to channel. 
   You have to compute an interprocedural cfg first *)


let d_cfgedge chan src dest =
  Printf.fprintf chan "%i -> %i" src.sid dest.sid

let d_cfgnode chan (s : stmt) =
  Printf.fprintf chan "%i [label=\"%i: %s\"]\n\t" s.sid s.sid (statement2str s.skind);
  List.iter (fun suc ->(d_cfgedge chan s suc); Printf.fprintf chan "\n\t") s.succs  

(** print control flow graph (in dot form) for methdec to channel *)
(* ddino: I think it can be simplified if we print everything in terms of nodes instead of stmts *)
let print_cfg_channel (chan : out_channel) (md : methdec) =
  let pnode (s:stmt) =  d_cfgnode chan s
  in forallStmts pnode md;
  let minfo= mcfginfo_tbl_find (key_method md) in
  let sn= method_cfg_info_get_start_node minfo in
  Printf.fprintf chan "%i [label=\"%i: Method %s START\"]\n\t" (node_get_id sn) (node_get_id sn) (name2str md.name); 
  List.iter (fun suc ->(d_cfgedge chan sn.nd_stmt suc); Printf.fprintf chan "\n\t") sn.nd_stmt.succs;    
  let en= method_cfg_info_get_exit_node minfo in
  Printf.fprintf chan "%i [label=\"%i: Method %s EXIT\"]\n\t" (node_get_id en) (node_get_id en) (name2str md.name); 
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

(* ================== END of Printing dotty files ================== *)

let compute_icfg mdecs = 
  icfg_create_method_cfg_infos mdecs;
  List.iter icfg_build_intra_cfg mdecs;
  icfg_compute_node_edges ();
  print_icfg_dotty mdecs

