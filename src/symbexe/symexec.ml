(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


open Pterm
open Plogic
open Rlogic
open Jlogic
open Global_types
open Jparsetree
open Cfg_core
open Prover
open Specification
open Vars
open Support_symex

(* global variables *)
let curr_meth = ref ""
let curr_logic: Prover.logic ref = ref Prover.empty_logic
let curr_abs_rules: Prover.logic ref = ref Prover.empty_logic
(*let curr_static_methodSpecs:Specification.methodSpecs ref = ref Specification.emptyMSpecs *)
let curr_dynamic_methodSpecs:Specification.methodSpecs ref = ref Specification.emptyMSpecs


(* create local program variables for methods. 
   mdl is the list of all methods in the class file.
   A special return variable (called method_name$ret) is created as well.
 *)
let create_program_variables mdl =
  let process_method md =
    let lv=snd (List.split md.locals) in
    let lv = List.map (fun v -> Var_name v) lv in
    let lv = Var_name(Identifier_name(name_ret_var))::lv in
    let locs= List.map (fun v -> variable2key v, Vars.concretep_str (variable2key v)) lv in
    List.iter (fun (k,v) -> var_table_add k v) locs
  in 
  List.iter process_method mdl




(* ================  transition system ==================  *)

type id = int

let set_group,grouped = let x = ref false in (fun y -> x := y),(fun () -> !x )

let fresh_node = let node_counter = ref 0 in fun () ->  let x = !node_counter in node_counter := x+1; x

let fresh_file = let file_id = ref 0 in fun () -> let x = !file_id in file_id := x+1;  Sys.getcwd() ^  "/" ^ !file ^ ".proof_file_"^(string_of_int x)^".txt"


type node = {mutable content : string; id : id; mutable ntype : ntype; mutable url : string; mutable edges : edge list; cfg : Cfg_core.node_core option}
and  edge = string * string * node * node * string option

let graphe = ref []


let mk_node c id nt url ed cfg =
 { content =c; 
   id =id; 
   ntype =nt; 
   url =url; 
   edges =ed; 
   cfg =cfg
 }

let node_get_content (n:node) : string = 
  n.content 

let node_get_idd (n:node) : id = 
  n.id 

let node_get_ntype (n:node) : ntype = 
  n.ntype 

let node_get_url (n:node) : string = 
  n.url 


module Idmap = 
  Map.Make(struct 
	     type t = int option 
	     let compare = compare
	   end)

let graphn = ref  Idmap.empty
let startnodes : node list ref = ref []

let make_start_node node = startnodes := node::!startnodes

let escape_for_dot_label s =
  Str.global_replace (Str.regexp "\\\\n") "\\l" (String.escaped s)

let pp_dotty_transition_system () =
  let foname = (!file) ^ ".execution_core.dot~" in
  let dotty_outf=open_out foname in
  if Config.symb_debug() then Printf.printf "\n Writing transition system file execution_core.dot  \n";
  Printf.fprintf dotty_outf "digraph main { \nnode [shape=box,  labeljust=l];\n\n";
  Idmap.iter 
    (fun cfg nodes ->
      ((
       if grouped () then match cfg with Some cfg -> Printf.fprintf dotty_outf "subgraph cluster_cfg%i {\n"  cfg | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=escape_for_dot_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	| Plain -> ()
	| Good ->  ()
	| Error ->  ()
	| UnExplored -> ()
	| Abs ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=yellow, style=filled%s]\n" id label url)
	nodes;
      if grouped () then match cfg with Some _ -> Printf.fprintf dotty_outf "\n}\n" | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=escape_for_dot_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	  Plain ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l%s]\n" id label url
	| Good ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=green, style=filled%s]\n" id label url
	| Error ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=red, style=filled%s]\n" id label url
	| UnExplored ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=orange, style=filled%s]\n" id label url
	| Abs -> () )
	nodes;
    )
    !graphn;
  List.iter (fun (l,c,s,d, o) ->
    let l = escape_for_dot_label l in
    let c = escape_for_dot_label c in
    Printf.fprintf dotty_outf "\n state%i -> state%i [label=\"%s\", tooltip=\"%s\"%s]" s.id d.id l c
	    (match o with 
	      None -> ""
	    | Some f -> Printf.sprintf ", URL=\"file://%s\", fontcolor=blue" f))
    !graphe;
  Printf.fprintf dotty_outf "\n\n\n}";
  close_out dotty_outf;
  Sys.rename foname (!file ^ ".execution_core.dot")


let add_node (label : string) (ty : ntype) (cfg : Cfg_core.node_core option) = 
  let id = fresh_node () in 
  let node = {content=label; id=id;ntype=ty;url=""; edges=[]; cfg = cfg} in 
  let cfgid = 
    match cfg with 
      None -> None 
    | Some cfg -> Some (node_get_id cfg) in 
  graphn := Idmap.add cfgid (node::(try Idmap.find cfgid !graphn with Not_found -> [])) !graphn;
  node

let add_error_node label = add_node label Error None
let add_abs_node label cfg = add_node label Abs (Some cfg)
let add_good_node label = add_node label Good None
let add_node_unexplored label cfg = add_node label UnExplored (Some cfg)
let add_node label cfg = add_node label UnExplored (Some cfg)

let explore_node src = if src.ntype = UnExplored then src.ntype <- Plain

let add_abs_heap_node (heap : Rlogic.ts_form) cfg= 
  (Format.fprintf (Format.str_formatter) "%a" string_ts_form heap);
  add_abs_node (Format.flush_str_formatter ()) cfg

let add_heap_node (heap : Rlogic.ts_form) cfg = 
  (Format.fprintf (Format.str_formatter) "%a" string_ts_form heap);
  add_node (Format.flush_str_formatter ()) cfg

let add_error_heap_node (heap : Rlogic.ts_form) = 
  (Format.fprintf (Format.str_formatter) "%a" string_ts_form heap);
  add_error_node (Format.flush_str_formatter ())

let x = ref 0


let add_edge src dest label = 
  let edge = (label, "", src, dest, None) in
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  explore_node src;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1


let add_edge_with_proof src dest label = 
  let f = fresh_file() in
  let out = open_out f in
  Prover.pprint_proof out;
  close_out out;
  explore_node src;
  let edge = (label, "", src, dest, Some f) in 
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1

(*let add_edge_with_string_proof src dest label proof = 
  let f = fresh_file() in
  let out = open_out f in
  output_string out proof;
  close_out out;
  graphe := (label, src, dest, Some f)::!graphe*)

let add_url_to_node src proof = 
  let f = fresh_file() in
  let out = open_out f in
  List.iter (output_string out) proof;
  close_out out;
  src.url <- f

let add_id_form h cfg =
    let id=add_heap_node h cfg in
    (h,id)

let add_id_formset sheaps cfg =  List.map (fun h -> add_id_form h cfg) sheaps

let add_id_abs_form cfg h =
    let id=add_abs_heap_node h cfg in
    (h,id)

let add_id_abs_formset sheaps cfg =  List.map (add_id_abs_form cfg) sheaps


(* ================   ==================  *)


(* ================  work list algorithm ==================  *)

(* this type has support for  creating a transition system 
   (formula, id)
   id is a unique identifier of the formula
 *)
type formset_entry = Rlogic.ts_form * node

(* eventually this should be a more efficient data structure than list*)
type formset = formset_entry list 


type formset_hashtbl = (int, formset) Hashtbl.t

(* table associating a cfg node to a set of heaps *)
let formset_table : formset_hashtbl = Hashtbl.create 10000


let formset_table_add key s = 
  Hashtbl.add formset_table key s

let formset_table_replace key s = 
  Hashtbl.replace formset_table key s

let formset_table_mem key  = 
  Hashtbl.mem formset_table key 

let formset_table_find key =
  try 
    Hashtbl.find formset_table key
  with Not_found -> 
    warning(); let _ =Printf.printf "\n ERROR: cannot find formset for %i in the table. Abort! \n" key in
    reset(); assert false

let remove_id_formset formset =
  fst (List.split formset)


let rec param_sub il num sub = 
  match il with 
    [] -> sub
  | i::il -> param_sub il (num+1) (add (Vars.concretep_str (parameter num)) (immediate2args i) sub)



let param_sub il =
  let ret_var = concretep_str name_ret_var in 
  let sub' = add ret_var (Arg_var(var_table_find (name_ret_var)))  empty in 
  let this_var = concretep_str this_var_name in 
  let sub' = add this_var (Arg_var(var_table_find (this_var_name)))  sub' in 
  match il with Some il -> param_sub il 0 sub' | None -> sub'
  


let param_this_sub il n = 
  let sub = param_sub il in 
  let nthis_var = concretep_str Support_syntax.this_var_name in 
  add nthis_var (name2args n)  sub 
 

let call_jsr_static (sheap,id) spec il node = 
  let sub' = param_sub il in
  let sub''= freshening_subs sub' in
  let spec'=Specification.sub_spec sub'' spec  in 
  let res = (jsr !curr_logic sheap spec') in
    match res with 
      None -> Printf.printf "\n\n I cannot find splitting to apply spec. Giving up! \n\n"; assert false
    | Some r -> fst r


let call_jsr (sheap,id) spec n il si node = 
  let sub' = param_this_sub il n in 
  let sub''= freshening_subs sub' in
  let spec'= Specification.sub_spec sub'' spec  in 
  let res = (jsr !curr_logic sheap spec') in
    match res with 
      None ->   
	let idd = add_error_node "ERROR" in
	add_edge_with_proof id idd 	
	  (Format.fprintf 
	     (Format.str_formatter) "%s:@\n %a" 
	     (Pprinter_core.statement_core2str (node_get_stmt node).skind) 
	     Prover.pprint_counter_example (); 
	   Format.flush_str_formatter ());
        warning();
	Printf.printf "\n\nERROR: While executing node %d:\n   %s\n"  (node_get_id node) (Pprinter_core.statement_core2str (node_get_stmt node).skind);
	Prover.print_counter_example ();
	reset(); 
	[]
	(*assert false*)
(*	  "Preheap:\n    %s\n\nPrecondition:\n   %s\nCannot find splitting to apply spec. Giving up! \n\n" sheap_string (Plogic.string_form spec.pre); assert false *)
    | Some r -> fst r




(* true if e is a variable starting with $ sign. They are special variable 
in jimple and need to e treated in special way  *)
let is_dollar_variable e =
  match e with 
    Immediate_local_name (Identifier_name x) -> 
      (String.sub x 0 1) = "$" 
  | _ -> false


let immediate2var e = 
  match immediate2args e with 
    Arg_var v -> v
  | _ -> assert false



(* checks if x \in fset. membership is considered up to logical equivalence *)
let rec formset_mem lo x fset =
  match fset with 
  | [] -> false
  | y::fset' -> 
      ((check_implication lo x y) && (check_implication lo y x)) || (formset_mem lo x fset') 

let compact_formset lo xs = 
  let rec impl xs ys = 
    match ys with 
      [] -> xs
    | y::ys -> 
	let xs = List.filter 
	    (fun x -> 
	      if (Prover.check_implication lo x y) then false else true) xs in 
	let ys = List.filter 
	    (fun x -> 
	      if (Prover.check_implication lo x y) then false else true) ys in 
	impl (y::xs) ys
  in (*Debug.debug_ref:=true; *)let xs = impl [] xs in (*Debug.debug_ref:=false;*) xs

(** implements s1 U s2  *)
let rec union_formsets lo s2 s1 =
(*  compact_formset lo (s2@s1)*)
  match s1 with 
  | [] -> s2
  | s::s1' -> 
      if (formset_mem lo s s2) then 
	union_formsets lo s2 s1'  
      else s::(union_formsets lo s2 s1') 

let worklist = ref []

let add_worklist n = 
  worklist := n::!worklist

exception Contained


let check_postcondition m heaps sheap =
  let sheap_noid=fst sheap in  
  try 
    let heap,id = List.find (fun (heap,id) -> (check_implication_frame !curr_logic sheap_noid heap)!=[]) heaps in
    if Config.symb_debug() then 
      Printf.printf "\n\nPost okay %s \n" (Pprinter.name2str m.name_m);
    (*	let idd = add_good_node ("EXIT: "^(Pprinter.name2str m.name)) in *)
    add_edge_with_proof (snd sheap) id "exit";
    (*	add_edge id idd "";*)
  with Not_found -> 
    warning();
    let _= Printf.printf "\n\nERROR: cannot prove post for method %s\n" (Pprinter.name2str m.name_m) in
    Prover.print_counter_example ();
    reset();
    List.iter (fun heap -> 
		 let idd = add_error_heap_node (fst heap) in 
		 add_edge_with_proof (snd sheap) idd 
		   (Format.fprintf 
		      (Format.str_formatter) "ERROR EXIT: %s:@\n %a" 
		      (Pprinter.name2str m.name_m) 
		      Prover.pprint_counter_example (); 
		    Format.flush_str_formatter ()))
      heaps
      (*print_formset "\n\n Failed Heap:\n" [sheap]    *)

      

let rec exec n sheap = 
  let sheap_noid=fst sheap in
  Rlogic.kill_all_exists_names sheap_noid;
(*  if Config.symb_debug() then 
    Format.printf "Output to %i with heap@\n   %a@\n" (node_get_id n) (string_ts_form (Rterm.rao_create ())) sheap_noid; *)
  execute_core_stmt n sheap 


and execs_one n sheaps = 
  let rec f ls = 
    match ls with 
    | [] -> [] 
    | s::ls' ->  List.flatten(List.map (exec s) sheaps) @ (f ls') 
  in
  let succs=node_get_succs n in
  f succs

and execute_core_stmt n (sheap : formset_entry) : formset_entry list =
  let sheap_noid=fst sheap in
  Rlogic.kill_all_exists_names sheap_noid;
  let stm=node_get_stmt n in
  if Config.symb_debug() then 
    Format.printf "@\nExecuting statement:@ %s" (Pprinter_core.statement_core2str stm.skind); 
(*  if Config.symb_debug() then 
    Format.printf "@\nwith heap:@\n    %a@\n@\n@."  (string_ts_form (Rterm.rao_create ())) sheap_noid; *)
  if (Prover.check_inconsistency !curr_logic (form_clone sheap_noid false)) then 
    (if Config.symb_debug() then Printf.printf "\n\nInconsistent heap. Skip it!\n";
     let idd = add_good_node "Inconsistent"  in add_edge_with_proof (snd sheap) idd "proof";
     [])
  else (
    if Config.symb_debug() then 
      Printf.printf "\nStarting execution of node %i \n" (node_get_id n);
    match n.nd_kind with 
    | Exit_node -> 
	if Config.symb_debug() then Printf.printf "Exit node %i\n" (node_get_id n);
	(* Check implies post-condtion *)
	let m = match n.nd_method with Some x -> x.pd_md | _ -> assert false in 
	let heaps= formset_table_find (node_get_id n) in
	check_postcondition m heaps sheap; 	
	[]
    | _ -> 
	(*  let minfo=node_get_method_cfg_info n in *)
	let id_clone h = (form_clone (fst h) false, snd h) in 
	if Config.symb_debug() then 
	  Format.printf "@\nExecuting statement:@ %s%!" (Pprinter_core.statement_core2str stm.skind); 
(*	if Config.symb_debug() then 
	  Format.printf "@\nwith heap:@\n    %a@\n@\n%!"  (string_ts_form (Rterm.rao_create ())) sheap_noid; *)
	(match stm.skind with 
 	 | Label_stmt_core l -> 
	     (*  Update the labels formset, if sheap already implied then fine, otherwise or it in. *)
	     (let id = node_get_id n in 
	      try
(*		if Config.symb_debug() then Format.printf "@\nPre-abstraction:@\n    %a@."  (string_ts_form (Rterm.rao_create ())) sheap_noid; *)
		let sheap_pre_abs = form_clone sheap_noid true in 
		let sheaps_abs = Prover.abs !curr_abs_rules sheap_pre_abs in 
		let sheaps_abs = List.map (fun x -> form_clone x true) sheaps_abs in 
		if Config.symb_debug() then Format.printf "@\nPost-abstractionc count:@\n    %d@."  (List.length sheaps_abs);
		List.iter Rlogic.kill_all_exists_names sheaps_abs;
(*		if Config.symb_debug() then List.iter (fun sheap -> Format.printf "@\nPost-abstraction:@\n    %a@."  (string_ts_form (Rterm.rao_create ())) sheap) sheaps_abs; *)
		
		let formset = (formset_table_find id) in 
(*		if Config.symb_debug() then (
		  Format.printf "Testing inclusion of :@    %a" 
		    (Debug.list_format "@\n" (string_ts_form (Rterm.rao_create ()))) sheaps_abs;
		  print_formset "in " (remove_id_formset formset)
		); *)
		explore_node (snd sheap);
		let sheaps_with_id = add_id_abs_formset sheaps_abs n in
		List.iter (fun sheap2 ->  add_edge_with_proof (snd sheap) (snd sheap2) ("Abstract@"^Pprinter_core.statement_core2str stm.skind)) sheaps_with_id;
		let sheaps_with_id = List.filter 
		  (fun (sheap2,id2) -> 
		     (let s = ref [] in 
		      if  
			(List.for_all
			   (fun (form,id) -> 
			      if check_implication_frame !curr_logic (form_clone sheap2 false) form  != []then 
				(add_edge_with_proof id2 id ("Contains@"^Pprinter_core.statement_core2str stm.skind); false) 
			      else (s := ("\n---------------------------------------------------------\n" ^ (string_of_proof ())) :: !s; true))
			   formset)
		      then ( 
			if !s != [] then (add_url_to_node id2 !s); true
		      ) else false
		     )
		  )
		  sheaps_with_id in
		(*	    List.iter (fun h ->
			    add_edge (snd sheap) (snd h) (Pprinter.statement2str stm.skind)) sheaps_with_id;*)
		formset_table_replace id (sheaps_with_id @ formset);
		execs_one n (List.map id_clone sheaps_with_id)
	      with Contained -> 
		if Config.symb_debug() then Printf.printf "Formula contained.\n"; [])
	 | If_stmt_core(e,l) ->
	     let succs=node_get_succs n in
	     let sheap2 = (form_clone (fst sheap) false, snd sheap) in 
	     (match succs with
	      | [s1;s2] ->  
		  (match s1.nd_stmt.skind with
		   | Label_stmt_core l' when l'=l -> 
		       let cc_h=(conj_convert (expression2pure e) (fst sheap)) in
		       let cc_h_id = add_id_form cc_h n in 
		       add_edge (snd sheap) (snd cc_h_id) (Pprinter.expression2str e);
		       let cc_h2=(conj_convert (expression2pure (negate e)) (fst sheap2)) in
		       let cc_h2_id = add_id_form cc_h2 n in 
		       add_edge (snd sheap) (snd cc_h2_id) (Pprinter.expression2str (negate e));
		       let h1=exec s1 cc_h_id in
		       let h2=exec s2 (cc_h2_id) in 
		       h1 @ h2
		   | _ -> 
		       let cc_h=(conj_convert (expression2pure (negate e)) (fst sheap)) in
		       let cc_h_id = add_id_form cc_h n in 
		       add_edge (snd sheap) (snd cc_h_id) (Pprinter.expression2str (negate e));
		       let cc_h2=(conj_convert (expression2pure e) (fst sheap2)) in
		       let cc_h2_id = add_id_form cc_h2 n in 
		       add_edge (snd sheap) (snd cc_h2_id) (Pprinter.expression2str e);
		       let h1=exec s1 cc_h_id in
		       let h2=exec s2 (cc_h2_id) in
		       h1 @ h2
		  )
	      | _ -> assert false )

	 | Goto_stmt_core _ -> execs_one n [sheap]
	 | Nop_stmt_core  -> execs_one n [sheap]
	 | Assignment_core (vl, spec, il) -> 
	    ( match vl with 
	     | [] -> 
		 let hs=call_jsr_static sheap spec il n in
		 let hs=add_id_formset hs n in
		 execs_one n hs
	     | [v] ->
		 let ret_var = var_table_find (name_ret_var) in
		 let v_var=variable2var v in
		 let eliminate_ret_var h =
		   let h = update_var_to v_var (Arg_var ret_var) h in 
		   kill_var ret_var h;
		   h
		 in
		 let hs=call_jsr_static sheap spec il n in
		 let hs=List.map eliminate_ret_var hs in 
		 let hs=add_id_formset hs n in
		 execs_one n hs
	     | _ -> assert false (* do be done *)
	    )
	 | Throw_stmt_core _ -> assert  false 
	 | _ -> assert false
	))



let initialize_method_forms method_forms = 
  let initialize_method_starting_node (m,initial_form,final_form) = 
    let minfo=Cfg_core.mcfginfo_tbl_find (key_method m) in
    let start_node=method_cfg_info_get_start_node minfo in
    let end_node=method_cfg_info_get_exit_node minfo in
    let meth_initial_form_noid = initial_form in
    let meth_initial_form = add_id_form meth_initial_form_noid start_node in 
    let id = add_good_node ("METHOD: "^(Pprinter.name2str m.name_m)) in 
    make_start_node id;
    let id_exit = add_good_node ("EXIT: "^(Pprinter.name2str m.name_m)) in 
    add_edge id (snd meth_initial_form) "";
    let meth_initial_formset =  [meth_initial_form] in
    let meth_final_formset_noid = [final_form] in 
    let meth_final_formset = add_id_formset meth_final_formset_noid end_node in
    List.iter (fun (_,id) -> add_edge id id_exit "") meth_final_formset; 
    if Config.symb_debug () then print_formset ("\n"^(Pprinter.name2str m.name_m)^" init_form=") [meth_initial_form_noid] ;
    if Config.symb_debug () then print_formset ("\n"^(Pprinter.name2str m.name_m)^" final_form=") meth_final_formset_noid ;
    formset_table_replace (node_get_id start_node) meth_initial_formset;
    formset_table_replace (node_get_id end_node) meth_final_formset;
  in
  List.iter (fun n -> formset_table_add (node_get_id n) []) (Cfg_core.get_all_nodes ());
  List.iter initialize_method_starting_node method_forms


    
let nodes_meth2list md =
  let rec collect tovisit collected =
    match tovisit with
    | [] -> collected 
    | n::tovisit' -> 
	if List.mem n collected  then 
	  collect tovisit' collected
	else collect ((node_get_succs n) @ tovisit') (n::collected) 
  in
  let minfo=Cfg_core.mcfginfo_tbl_find (key_method md) in
  let sn=method_cfg_info_get_start_node minfo in
  collect [sn] []



let rec icfg_nodes2list mdl = 
  match mdl with
  |[] -> []
  | md::mdl' ->
      (List.rev (nodes_meth2list md)) @ icfg_nodes2list mdl' 



(* implements a work-list fidex point algorithm *)
(* the queue qu is a list of pairs [(node, expression option)...] the expression
is used to deal with if statement. It is the expression of the if statement is the predecessor
of the node is a if_stmt otherwise is None. In the beginning is always None for each node *)
 let compute_fixed_point cname mdl method_forms 
(apfmap : logic Spec_def.ClassMap.t) (lo : logic) (abs_rules : logic)
(sspecs: Specification.methodSpecs) (dspecs: Specification.methodSpecs)  =
  let sspecs_prog = MethodMap.map (logical_vars_to_prog) sspecs in  
  curr_dynamic_methodSpecs:=dspecs;
  (* remove methods that are declared abstraction *)
  let mdl = List.filter (fun y -> List.for_all (fun x-> Abstract<>x) (y.modifiers)) mdl in
  let lo = try let x=Spec_def.ClassMap.find cname apfmap in x with Not_found -> lo in
  curr_logic:= lo;
  curr_abs_rules:=abs_rules;
  compute_icfg mdl;
  create_program_variables mdl; 
  initialize_method_forms method_forms;  
  worklist := List.filter (fun n -> (if Config.symb_debug() then print_node n); match n.nd_kind with Start_node -> (if Config.symb_debug() then Printf.printf "Start node %i\n" (node_get_id n));true | _ -> false) (icfg_nodes2list mdl);
  while (!worklist<>[]) do 
    let v=List.hd !worklist in
    worklist := List.tl !worklist;
    let _=List.map (fun f -> execute_core_stmt v f) (formset_table_find (node_get_id v)) in ();
    if Config.symb_debug() then Printf.printf "\nEnd execution of node %i \n" (node_get_id v)
  done 


