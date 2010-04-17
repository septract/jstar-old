(********************************************************
   This file is part of jStar 
	src/symbexe/symexec.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

open Cfg_core
open Methdec_core
open Psyntax
open Sepprover
open Spec
open Specification
open Vars


(* global variables *)

let curr_logic : Psyntax.logic ref = ref Psyntax.empty_logic
let curr_abs_rules : Psyntax.logic ref = ref Psyntax.empty_logic





(* ================  transition system ==================  *)
type ntype = 
    Plain | Good | Error | Abs | UnExplored

type id = int

let file = ref ""

let set_group,grouped = let x = ref false in (fun y -> x := y),(fun () -> !x )

let fresh_node = let node_counter = ref 0 in fun () ->  let x = !node_counter in node_counter := x+1; x

let fresh_file = let file_id = ref 0 in fun () -> let x = !file_id in file_id := x+1;  Sys.getcwd() ^  "/" ^ !file ^ ".proof_file_"^(string_of_int x)^".txt"


type node = {mutable content : string; id : id; mutable ntype : ntype; mutable url : string; mutable edges : edge list; cfg : stmt_core option}
and  edge = string * string * node * node * string option
  (** An edge has a label, a ???, source, target, and perhaps an URL. *)

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

let pp_dotty_transition_system () =
  let foname = (!file) ^ ".execution_core.dot~" in
  let dotty_outf=open_out foname in
  if Config.symb_debug() then Printf.printf "\n Writing transition system file execution_core.dot  \n";
  Printf.fprintf dotty_outf "digraph main { \nnode [shape=box,  labeljust=l];\n\n";
  Idmap.iter 
    (fun cfg nodes -> (
      (* Print Abs nodes. *)
      (if grouped () then 
        match cfg with Some cfg -> Printf.fprintf dotty_outf "subgraph cluster_cfg%i {\n"  cfg | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=Dot.escape_for_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	| Plain -> ()
	| Good ->  ()
	| Error ->  ()
	| UnExplored -> ()
	| Abs ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=yellow, style=filled%s]\n" id label url)
	nodes;
      if grouped () then match cfg with Some _ -> Printf.fprintf dotty_outf "\n}\n" | _ -> ());
      (* Print non-Abs nodes. *)
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=Dot.escape_for_label label in
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
  List.iter (fun (l,c,s,d,o) ->
    let l = Dot.escape_for_label l in
    let c = Dot.escape_for_label c in
    Printf.fprintf dotty_outf "\n state%i -> state%i [label=\"%s\", tooltip=\"%s\"%s]" s.id d.id l c
	    (match o with 
	      None -> ""
	    | Some f -> Printf.sprintf ", URL=\"file://%s\", fontcolor=blue" f))
    !graphe;
  Printf.fprintf dotty_outf "\n\n\n}";
  close_out dotty_outf;
  let fname = (!file) ^ ".execution_core.dot" in
  if Sys.file_exists fname then Sys.remove fname;
  Sys.rename foname (!file ^ ".execution_core.dot")


let add_node (label : string) (ty : ntype) (cfg : stmt_core option) = 
  let id = fresh_node () in 
  let node = {content=label; id=id;ntype=ty;url=""; edges=[]; cfg = cfg} in 
  let cfgid = 
    match cfg with 
      None -> None 
    | Some cfg -> Some (cfg.sid) in 
  graphn := Idmap.add cfgid (node::(try Idmap.find cfgid !graphn with Not_found -> [])) !graphn;
  node

let add_error_node label = add_node label Error None
let add_abs_node label cfg = add_node label Abs (Some cfg)
let add_good_node label = add_node label Good None
let add_node_unexplored label cfg = add_node label UnExplored (Some cfg)
let add_node label cfg = add_node label UnExplored (Some cfg)

let explore_node src = if src.ntype = UnExplored then src.ntype <- Plain

let add_abs_heap_node (heap : Sepprover.inner_form) cfg= 
  (Format.fprintf (Format.str_formatter) "%a" Sepprover.string_inner_form heap);
  add_abs_node (Format.flush_str_formatter ()) cfg

let add_heap_node (heap : inner_form) cfg = 
  (Format.fprintf (Format.str_formatter) "%a" Sepprover.string_inner_form heap);
  add_node (Format.flush_str_formatter ()) cfg

let add_error_heap_node (heap : inner_form) = 
  (Format.fprintf (Format.str_formatter) "%a" Sepprover.string_inner_form heap);
  add_error_node (Format.flush_str_formatter ())

let x = ref 0


let add_edge src dest label = 
  let edge = (label, "", src, dest, None) in
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  explore_node src;
  x := (!x + 1) mod 5;
  if !x = 0 then pp_dotty_transition_system ()


let add_edge_with_proof src dest label = 
  let f = fresh_file() in
  let out = open_out f in
  Sepprover.pprint_proof out;
  close_out out;
  explore_node src;
  let edge = (label, "", src, dest, Some f) in 
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1

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

let add_id_formset_edge src label sheaps cfg =  
  match sheaps with 
    [] ->
      if Config.symb_debug() then Printf.printf "\n\nInconsistent heap. Skip it!\n";
      let idd = add_good_node "Inconsistent" in add_edge_with_proof src idd (label ^"\n Inconsistent");
	[]
  | _ -> 
  let sheaps_id = add_id_formset sheaps cfg in
  List.iter (fun dest -> add_edge_with_proof src (snd dest) label) sheaps_id;
  sheaps_id

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
type formset_entry = inner_form * node

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
    []  (* Default case return false, empty list of disjunctions *)


let remove_id_formset formset =
  fst (List.split formset)

let parameter n = "@parameter"^(string_of_int n)^":"

let name_ret_var = "$ret_var"

let ret_var = Vars.concretep_str name_ret_var 


let rec param_sub il num sub = 
  match il with 
    [] -> sub
  | i::il -> param_sub il (num+1) (add (Vars.concretep_str (parameter num)) (i) sub)



let param_sub il =
  let sub' = add ret_var (Arg_var(ret_var))  empty in 
  param_sub il 0 sub'
  


let id_clone h = (form_clone (fst h), snd h)



let call_jsr_static (sheap,id) spec il node = 
  let sub' = param_sub il in
  let sub''= (*freshening_subs*) sub' in
  let spec'= Specification.sub_spec sub'' spec  in 
  let res = (jsr !curr_logic sheap spec') in
    match res with 
      None ->   
	let idd = add_error_node "ERROR" in
	add_edge_with_proof id idd 	
	  (Format.fprintf 
	     (Format.str_formatter) "%a:@\n %a" 
	     Pprinter_core.pp_stmt_core node.skind
	     Sepprover.pprint_counter_example (); 
	   Format.flush_str_formatter ());
        System.warning();
	Format.printf "\n\nERROR: While executing node %d:\n   %a\n"  
	  (node.sid) 
	  Pprinter_core.pp_stmt_core node.skind;
	Sepprover.print_counter_example ();
	System.reset(); 
	[]
	(*assert false*)
(*	  "Preheap:\n    %s\n\nPrecondition:\n   %s\nCannot find splitting to apply spec. Giving up! \n\n" sheap_string (Plogic.string_form spec.pre); assert false *)
    | Some r -> fst r





exception Contained


let check_postcondition heaps sheap =
  let sheap_noid=fst sheap in  
  try 
    let heap,id = List.find (fun (heap,id) -> (frame !curr_logic (form_clone sheap_noid) heap)!=None) heaps in
    if Config.symb_debug() then 
      Printf.printf "\n\nPost okay \n";
    (*	let idd = add_good_node ("EXIT: "^(Pprinter.name2str m.name)) in *)
    add_edge_with_proof (snd sheap) id "exit";
    (*	add_edge id idd "";*)
  with Not_found -> 
    System.warning();
    let _= Printf.printf "\n\nERROR: cannot prove post\n"  in
    Sepprover.print_counter_example ();
    System.reset();
    List.iter (fun heap -> 
                 let form = Sepprover.convert (fst heap) in 
		 match form with 
		   None -> () 
		 | Some form -> 
		     let idd = add_error_heap_node form in 
		     add_edge_with_proof (snd sheap) idd 
		       (Format.fprintf 
			  (Format.str_formatter) "ERROR EXIT: @\n %a" 
			  Sepprover.pprint_counter_example (); 
			Format.flush_str_formatter ()))
      heaps


let rec exec n sheap = 
  let sheap_noid=fst sheap in
  let sheap_noid=Sepprover.kill_all_exists_names sheap_noid in 
  let sheap = (sheap_noid, snd sheap) in 
(*  if Config.symb_debug() then 
    Format.printf "Output to %i with heap@\n   %a@\n" (node_get_id n) (string_ts_form (Rterm.rao_create ())) sheap_noid; *)
  execute_core_stmt n sheap 

and execs_with_function n sheaps g = 
 let rec f ls = 
    match ls with 
    | [] -> []
    | [s] ->  List.flatten (List.map (exec s) sheaps)
    | s::ls' ->  List.flatten(List.map (fun h -> exec s (id_clone h)) sheaps) @ (f ls') 
  in
  let succs=g n in
  match succs with 
    [] -> 
      if Config.symb_debug() then Printf.printf "Exit node %i\n" (n.sid);
      sheaps
  |  _ -> f succs

and execs_one n sheaps =
	execs_with_function n sheaps (fun n -> if n.skind = End then [] else n.succs)
	
and execs n sheaps =
	execs_with_function n sheaps (fun n -> [n])

and execute_core_stmt n (sheap : formset_entry) : formset_entry list =
  let sheap_noid=fst sheap in
  let sheap_noid = Sepprover.kill_all_exists_names sheap_noid in 
  let stm=n in
  if Config.symb_debug() then 
    Format.printf "@\nExecuting statement:@ %a" Pprinter_core.pp_stmt_core stm.skind; 
  if Config.symb_debug() then 
    Format.printf "@\nwith heap:@\n    %a@\n@\n@."  string_inner_form  sheap_noid; 
  (
   if Config.symb_debug() 
   then begin
     Printf.printf "\nStarting execution of node %i \n" (n.sid);
     Format.printf "@\nExecuting statement:@ %a%!" Pprinter_core.pp_stmt_core stm.skind; 
     Format.printf "@\nwith heap:@\n    %a@\n@\n%!"  string_inner_form sheap_noid; 
    end;
    (match stm.skind with 
    | Label_stmt_core l -> 
	     (*  Update the labels formset, if sheap already implied then fine, otherwise or it in. *)
	(let id = n.sid in 
	try
	  if Config.symb_debug() 
	  then Format.printf "@\nPre-abstraction:@\n    %a@."  string_inner_form  sheap_noid; 
	  let sheap_pre_abs = form_clone_abs sheap_noid in 
	  let sheaps_abs = Sepprover.abs !curr_abs_rules sheap_pre_abs in 
	  let sheaps_abs = List.map (fun x -> form_clone_abs x) sheaps_abs in 
	  if Config.symb_debug() 
	  then Format.printf "@\nPost-abstraction count:@\n    %d@."  (List.length sheaps_abs);
	  let sheaps_abs = List.map Sepprover.kill_all_exists_names sheaps_abs in 
	  if Config.symb_debug() 
	  then List.iter (fun sheap -> Format.printf "@\nPost-abstraction:@\n    %a@."  string_inner_form sheap) sheaps_abs; 
	  
	  let formset = (formset_table_find id) in 
(*		if Config.symb_debug() then (
   Format.printf "Testing inclusion of :@    %a" 
		    (Debug.list_format "@\n" (string_inner_form (Rterm.rao_create ()))) sheaps_abs;
   print_formset "in " (remove_id_formset formset)
   ); *)
	  explore_node (snd sheap);
	  let sheaps_with_id = add_id_abs_formset sheaps_abs n in
	  List.iter 
	    (fun sheap2 ->  
	      add_edge_with_proof 
		(snd sheap) 
		(snd sheap2) 
		("Abstract@"^(Debug.toString Pprinter_core.pp_stmt_core stm.skind))
	    ) 
	    sheaps_with_id;
	  let sheaps_with_id = List.filter 
	      (fun (sheap2,id2) -> 
		(let s = ref [] in 
		if  
		  (List.for_all
		     (fun (form,id) -> 
		       if frame_inner !curr_logic (form_clone sheap2) form  != None then 
			 (add_edge_with_proof id2 id ("Contains@"^(Debug.toString Pprinter_core.pp_stmt_core stm.skind)); false) 
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
    | Goto_stmt_core _ -> execs_one n [sheap]
    | Nop_stmt_core  -> execs_one n [sheap]
    | Assignment_core (vl, spec, il) -> 
	( match vl with 
	| [] -> 
	    let hs=call_jsr_static sheap spec il n in
	    let hs=add_id_formset_edge (snd sheap) (Debug.toString Pprinter_core.pp_stmt_core n.skind) hs n in
	    execs_one n hs
	| [v] ->
	    let eliminate_ret_var h =
	      let h = update_var_to v (Arg_var ret_var) h in 
	      let h = kill_var ret_var h in 
	      h
	    in
	    let hs=call_jsr_static sheap spec il n in
	    let hs=List.map eliminate_ret_var hs in 
	    let hs=add_id_formset_edge (snd sheap) (Debug.toString Pprinter_core.pp_stmt_core n.skind)  hs n in
	    execs_one n hs
	| _ -> assert false (* TODO be done *)
	      )
    | Throw_stmt_core _ -> assert  false 
    | End -> execs_one n [sheap]
	  ))
      
(* Implements a work-list fixed point algorithm. *)
(* the queue qu is a list of pairs [(node, expression option)...] the expression
is used to deal with if statement. It is the expression of the if statement is the predecessor
of the node is a if_stmt otherwise is None. In the beginning is always None for each node *)
let verify (mname : string) (stmts : stmt_core list)  (spec : spec) (lo : logic) (abs_rules : logic) =

  (* remove methods that are declared abstraction *)
  curr_logic:= lo;
  curr_abs_rules:=abs_rules;
 
  stmts_to_cfg stmts;
  match stmts with 
    [] -> assert false
  | s::stmts -> 
      let id = add_good_node ("Start "^mname) in  
      make_start_node id;
      match Sepprover.convert (spec.pre) with 
	None -> System.warning(); Printf.printf "False precondition for specification of %s." mname  ;System.reset()
      |	Some pre -> 
	  let post = execute_core_stmt s (pre, id) in 
	  let id_exit = add_good_node ("Exit") in 
	  List.iter 
	    (fun post -> 
	      check_postcondition [(spec.post,id_exit)] post) post


let verify_ensures (name : string) (stmts: stmt_core list) (post : Psyntax.pform) conjoin_with_res_true (oldexp_frames : inner_form list list) lo abs_rules =
  (* construct the specification of the ensures clause *)
	let rec conjoin_disjunctions (d1 : inner_form list) (d2 : inner_form list) : inner_form list =
		match d1 with
			| [] -> []
			| d1first::d1rest ->
				List.append (
					List.map (fun d -> Sepprover.conjoin_inner d1first d) d2
				) (conjoin_disjunctions d1rest d2)
	in
	let oldexp_results = List.fold_left (fun acc oldexp_res -> conjoin_disjunctions oldexp_res acc) [Sepprover.inner_truth] oldexp_frames in
	  (* substitute $ret_var in the post! *)
	let post = subst_pform (add ret_var (Arg_var(Vars.concretep_str (name_ret_var^"_post"))) empty) post in
	let ensures_preconds = List.map (fun oldexp_result -> Sepprover.conjoin post oldexp_result) oldexp_results in
	let ensures_postcond = conjoin_with_res_true post in
	(* now do the verification *)
	curr_logic:= lo;
  curr_abs_rules:=abs_rules;
  stmts_to_cfg stmts;
  match stmts with 
    [] -> assert false
  | s::stmts ->
      let id = add_good_node ("Start "^name) in  
      make_start_node id;
      let post = execs s (List.map (fun pre -> (pre,id)) ensures_preconds) in
      let id_exit = add_good_node ("Exit") in
      List.iter 
	(fun post -> 
	  check_postcondition [(ensures_postcond,id_exit)] post) post


let check_and_get_frame (heap,id) sheap =
  let sheap_noid=fst sheap in  
  let frame = frame_inner !curr_logic (form_clone sheap_noid) heap in
  match frame with 
    Some frame -> 
                 if Config.symb_debug() then 
                        (Printf.printf "\n\nOld expression okay \n";
                        add_edge_with_proof (snd sheap) id "exit";
                        frame)
                 else
                        frame
  | None -> 
                 (System.warning();
                 let _= Printf.printf "\n\nERROR: cannot prove frame for old expression\n"  in
                 Sepprover.print_counter_example ();
                 System.reset();
                 let idd = add_error_heap_node heap in 
		 add_edge_with_proof (snd sheap) idd 
		   (Format.fprintf 
		      (Format.str_formatter) "ERROR EXIT: @\n %a" 
		      Sepprover.pprint_counter_example (); 
                      Format.flush_str_formatter ());
                 [])


let get_frame (stmts : stmt_core list) (pre : Psyntax.pform) (lo : logic) (abs_rules : logic) = 
  curr_logic:= lo;
  curr_abs_rules:=abs_rules;
 
  stmts_to_cfg stmts;
  match stmts with 
    [] -> assert false
  | s::stmts -> 
		  let id = add_good_node ("Start") in  
      make_start_node id;
      let rlogic_pre = Sepprover.convert pre in
      match rlogic_pre with
	None -> System.warning(); Printf.printf "False precondition for specification."  ;System.reset(); []
      |	Some rlogic_pre ->
	  let post = match execute_core_stmt s (rlogic_pre, id) with
	  | [p] -> p
	  | [] -> assert false
	  | _ -> assert false  (* an old expression is guaranteed to have only one exit point *) 
	  in 
	  let id_exit = add_good_node ("Exit") in 
	  check_and_get_frame (rlogic_pre,id_exit) post
