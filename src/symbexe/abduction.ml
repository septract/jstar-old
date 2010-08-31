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

open Vars
open Psyntax
open Sepprover

open Spec
open Cfg_core
open Specification
open Methdec_core
open Specification
open Symexec


let abduct_logic : Psyntax.logic ref = ref Psyntax.empty_logic

let get_heap state =
  fst (fst state)
  
let get_antiframe state =
  snd (fst state)

let get_node state =
  snd state

let make_state heap antiframe node =
  ((heap, antiframe), node)

(* ((heap, antiframe), node) *)
type form_pair_set_entry = (inner_form * inner_form) * node

type form_pair_set = form_pair_set_entry list 

type form_pair_set_hashtbl = (int, form_pair_set) Hashtbl.t

(* table associating a cfg node to a set of (heap, antiframe) pairs *)
let form_pair_set_table : form_pair_set_hashtbl = Hashtbl.create 10000

let form_pair_set_table_add key s = 
  Hashtbl.add form_pair_set_table key s

let form_pair_set_table_replace key s = 
  Hashtbl.replace form_pair_set_table key s

let form_pair_set_table_mem key  = 
  Hashtbl.mem form_pair_set_table key 

let form_pair_set_table_find key =
  try 
    Hashtbl.find form_pair_set_table key
  with Not_found -> 
    []  (* Default case return false, empty list of disjunctions *)

let remove_id_form_pair_set formpairset =
  fst (List.split formpairset)

let form_pair_set_clone state = 
  ((form_clone (get_heap state), form_clone (get_antiframe state)), get_node state)

let add_id_form_pair_set_edge src label hs cfg =  
  match hs with 
    [] ->
    if Config.symb_debug() then Printf.printf "\n\nInconsistent heap. Skip it!\n";
    let idd = add_good_node "Inconsistent" in add_edge_with_proof src idd (label ^"\n Inconsistent");
    []
  | _ ->
    let (sheaps, safs) = List.split hs in
    let form_pairs_with_id = ref [] in 
    List.iter2
      (fun sheap saf -> 
      let (sheap, id) = add_id_abs_form cfg sheap in
      form_pairs_with_id := ((sheap, saf), id) :: !form_pairs_with_id;)
      sheaps safs;
    List.iter (fun dest -> add_edge_with_proof src (get_node dest) label) !form_pairs_with_id;
    !form_pairs_with_id


(* This is the function that performs the abduction! *)
let jsr_abduct logic (pre : inner_form) (pre_antiframe : inner_form) (spec : spec) : ((inner_form * inner_form) list) option  = 
  let ev = ev_spec spec in 
  let subst = subst_kill_vars_to_fresh_exist ev in 
  let spec = sub_spec subst spec in 
  match spec with
    {pre = spec_pre; post = spec_post; excep = _} -> 
      let frame_antiframe_list = Sepprover.abduction_opt logic (Some pre) spec_pre in 
      match frame_antiframe_list with
        None -> None
      |	Some frame_antiframe_list -> 
        let res = Misc.map_option 
          (fun (post, antiframe) -> 
            try Some (Sepprover.conjoin spec_post post, Sepprover.conjoin_inner pre_antiframe antiframe) 
            with Contradiction -> None) frame_antiframe_list in 
        let res = List.map (fun (ts1, ts2) -> 
          let ts1' = vs_fold (fun e ts -> kill_var e ts) ev ts1 in
          let ts2' = vs_fold (fun e ts -> kill_var e ts) ev ts2 in
          (ts1', ts2')) res in 
        Some (res)


let call_jsr_abduct_static ((sheap, saf), id) spec il node = 
  let sub' = param_sub il in
  let sub''= (*freshening_subs*) sub' in
  let spec'= Specification.sub_spec sub'' spec in 
  let res = (jsr_abduct !abduct_logic sheap saf spec') in
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
    | Some r -> r


let rec abduct n state = 
  let sheap_noid = get_heap state in
  let sheap_noid = Sepprover.kill_all_exists_names sheap_noid in 
  let saf_noid = get_antiframe state in
  let saf_noid = Sepprover.kill_all_exists_names saf_noid in 
  abduct_core_stmt n (make_state sheap_noid saf_noid (get_node state))

and abducts_with_function n states g = 
 let rec f ls = 
    match ls with 
    | [] -> []
    | [s] ->  List.flatten (List.map (abduct s) states)
    | s::ls' ->  List.flatten (List.map (fun state -> abduct s (form_pair_set_clone state)) states) @ (f ls') 
  in
  let succs = g n in
  match succs with 
    [] -> 
      if Config.symb_debug() then Printf.printf "Exit node %i\n" (n.sid);
      states
  |  _ -> f succs

and abducts n states =
	abducts_with_function n states (fun n -> if n.skind = End then [] else n.succs)
	
and abduct_core_stmt n (state : form_pair_set_entry) : form_pair_set_entry list =
  let sheap_noid = get_heap state in
  let sheap_noid = Sepprover.kill_all_exists_names sheap_noid in 
  let saf_noid = get_antiframe state in
  let saf_noid = Sepprover.kill_all_exists_names saf_noid in 
  let stm = n in
  if Config.symb_debug() then 
    Format.printf "@\nExecuting statement:@ %a" Pprinter_core.pp_stmt_core stm.skind; 
  if Config.symb_debug() then begin
    Format.printf "@\nwith heap :@\n    %a@\n@\n@."  string_inner_form sheap_noid; 
    Format.printf "@\nand antiframe :@\n    %a@\n@\n@."  string_inner_form saf_noid; 
  end;
  (
    if Config.symb_debug() 
    then begin
      Printf.printf "\nStarting execution of node %i \n" (n.sid);
      Format.printf "@\nExecuting statement:@ %a%!" Pprinter_core.pp_stmt_core stm.skind; 
      Format.printf "@\nwith heap:@\n    %a@\n@\n%!"  string_inner_form sheap_noid; 
      Format.printf "@\nand antiframe:@\n    %a@\n@\n%!"  string_inner_form saf_noid; 
    end;
    (match stm.skind with 
    | Label_stmt_core l -> 
      (let id = n.sid in 
      try
        if Config.symb_debug() 
        then begin
          Format.printf "@\nPre-abstraction heap:@\n    %a@."  string_inner_form  sheap_noid; 
          Format.printf "@\nPre-abstraction antiframe:@\n    %a@."  string_inner_form  saf_noid; 
        end;
        let sheap_pre_abs = form_clone_abs sheap_noid in 
        let sheaps_abs = Sepprover.abs !curr_abs_rules sheap_pre_abs in 
        let sheaps_abs = List.map (fun x -> form_clone_abs x) sheaps_abs in
        let saf_pre_abs = form_clone_abs saf_noid in 
        let safs_abs = Sepprover.abs !curr_abs_rules saf_pre_abs in 
        let safs_abs = List.map (fun x -> form_clone_abs x) safs_abs in
        if Config.symb_debug() 
        then begin
          Format.printf "@\nPost-abstraction heaps count:@\n    %d@."  (List.length sheaps_abs);
          Format.printf "@\nPost-abstraction antiframes count:@\n    %d@."  (List.length safs_abs);
        end;
        let sheaps_abs = List.map Sepprover.kill_all_exists_names sheaps_abs in 
        let safs_abs = List.map Sepprover.kill_all_exists_names safs_abs in 
        if Config.symb_debug() 
        then begin
          List.iter (fun sheap -> Format.printf "@\nPost-abstraction heaps:@\n    %a@."  string_inner_form sheap) sheaps_abs; 
          List.iter (fun saf -> Format.printf "@\nPost-abstraction antiframes:@\n    %a@."  string_inner_form saf) safs_abs; 
        end;
        
        let form_pair_set = (form_pair_set_table_find id) in 
        explore_node (get_node state);
        
        let (prev_sheaps, prev_safs) = List.split (fst (List.split form_pair_set)) in
        (* filter abstracted heaps with non-empty frames *)
        let sheaps = List.filter 
          (fun sheap2 -> 
            (List.for_all
              (fun sheap -> frame_inner !curr_logic (form_clone sheap2) sheap = None)
            prev_sheaps)
          )
          sheaps_abs in
        (* filter abstracted antiframes with non-empty frames *)
        let safs = List.filter 
          (fun saf2 -> 
            (List.for_all
              (fun saf -> frame_inner !curr_logic (form_clone saf2) saf = None)
            prev_safs)
          )
          safs_abs in
		    
        if Config.symb_debug() 
        then begin
        Printf.printf "\nsheaps length: %d!\n" (List.length sheaps);
        Printf.printf "\nsafs length: %d!\n" (List.length safs);
        end;
        
        let form_pairs_with_id = ref [] in 
        (* pair new antiframes with all existing+new frames *)
        List.iter
          (fun sheap ->
          List.iter
            (fun saf ->
            let (sheap, id) = add_id_abs_form n sheap in
            form_pairs_with_id := ((sheap, saf), id) :: !form_pairs_with_id;)
            safs)
          (prev_sheaps @ sheaps);
        (* pair old antiframes with new antiframes *)
        List.iter
          (fun sheap ->
          List.iter
            (fun saf ->
            let (sheap, id) = add_id_abs_form n sheap in
            form_pairs_with_id := ((sheap, saf), id) :: !form_pairs_with_id;)
            prev_safs)
          sheaps;
        form_pair_set_table_replace id (!form_pairs_with_id @ form_pair_set);
        abducts n (List.map form_pair_set_clone !form_pairs_with_id)
      with Contained -> 
        if Config.symb_debug() then Printf.printf "Formula contained.\n"; [])

    | Goto_stmt_core _ -> abducts n [state]

    | Nop_stmt_core  -> abducts n [state]

    | Assignment_core (vl, spec, il) -> 
        ( 
        let hs = call_jsr_abduct_static state spec il n in
        if Config.symb_debug() 
        then begin
          List.iter
          (fun (sheap, saf) ->
          Format.printf "@\nFrame:@\n    %a@."  string_inner_form sheap; 
          Format.printf "@\nAntiframe:@\n    %a@."  string_inner_form saf;)
          hs  
        end;
        match vl with 
        | [] -> 
          let hs = add_id_form_pair_set_edge (get_node state) (Debug.toString Pprinter_core.pp_stmt_core n.skind) hs n in
          abducts n hs
        | vs -> 
          let (sheaps, safs) = List.split hs in
          let sheaps = List.map (eliminate_ret_vs "$ret_v" vs) sheaps in 
          let safs = List.map (eliminate_ret_vs "$ret_v" vs) safs in 
          let hs = List.combine sheaps safs in
          let hs = add_id_form_pair_set_edge (get_node state) (Debug.toString Pprinter_core.pp_stmt_core n.skind) hs n in
          abducts n hs
        )

    | Throw_stmt_core _ -> assert false 

    | End -> abducts n [state]
	  )
  )


(* variant of check_postcondition from symexec.ml that operates on inner_form heaps instead of pform *)
let check_postcondition_inner heaps sheap : bool =
  let sheap_noid=fst sheap in  
  try 
    let heap,id = List.find (fun (heap,id) -> (frame_inner !curr_logic (form_clone sheap_noid) heap)!=None) heaps in
    if Config.symb_debug() then 
      Printf.printf "\n\nPost okay \n";
    (*	let idd = add_good_node ("EXIT: "^(Pprinter.name2str m.name)) in *)
    add_edge_with_proof (snd sheap) id "exit";
    true
    (*	add_edge id idd "";*)
  with Not_found -> 
    System.warning();
    let _= Printf.printf "\n\nERROR: cannot prove post\n"  in
    Sepprover.print_counter_example ();
    System.reset();
    List.iter (fun (form,id) -> 
      let idd = add_error_heap_node form in 
      add_edge_with_proof (snd sheap) idd 
        (Format.fprintf 
        (Format.str_formatter) "ERROR EXIT: @\n %a" 
        Sepprover.pprint_counter_example (); 
        Format.flush_str_formatter ()))
      heaps;
    false

(* variant of verify from symexec.ml that operates on inner_form spec instead of pform *)    
let verify_inner 
    (mname : string) 
    (stmts : stmt_core list)  
    (spec_pre : inner_form)
    (spec_post : inner_form)
    (lo : logic) 
    (abs_rules : logic) 
    : bool 
    =
  curr_logic:= lo;
  curr_abs_rules:=abs_rules;

  (* stmts_to_cfg stmts; *)
  match stmts with 
  | [] -> assert false; false
  | s::_ -> 
      let id = add_good_node ("Start "^mname) in  
      make_start_node id;
      match inconsistent !curr_logic spec_pre with 
        true -> System.warning(); Printf.printf "False precondition for specification of %s." mname; System.reset(); false
      |	false -> 
        let posts = execute_core_stmt s (spec_pre, id) in 
        let id_exit = add_good_node ("Exit") in
        if Config.symb_debug() 
        then begin
          Printf.printf "\nChecking posts...\n";        
          List.iter
          (fun (sheap,id) ->
          Format.printf "@\nPost:@\n    %a@."  string_inner_form sheap;)
          posts
        end;
        List.fold_right (fun succ b -> succ && b)
                          (List.map (fun post -> check_postcondition_inner [(spec_post, id_exit)] post) posts)
                          true

let bi_abduct 
    (mname : string) 
    (stmts : stmt_core list)  
    (spec : spec) 
    (symexec_lo : logic) 
    (abduct_lo : logic) 
    (abs_rules : logic) 
    : ((inner_form * inner_form) list) =
  curr_logic := symexec_lo;
  abduct_logic := abduct_lo;
  curr_abs_rules := abs_rules;
  let empty = 
    match convert mkEmpty with
      None -> assert false;
    | Some emp -> emp
    in
  stmts_to_cfg stmts;
  match stmts with 
  | [] -> []
  | s::_ -> 
      let id = add_good_node ("Start "^mname) in  
      make_start_node id;
      match Sepprover.convert (spec.pre) with 
        None -> System.warning(); Printf.printf "False precondition for specification of %s." mname; System.reset(); []
      |	Some pre -> 
        if Config.symb_debug() then 
          Printf.printf "\nStarting abduction...\n";
        let posts = fst (List.split (abduct_core_stmt s ((pre, empty), id))) in
        (* build spec pre/post pairs *)
        let specs = List.map 
          (fun (spec_post, antiframe) -> (Sepprover.conjoin_inner pre antiframe, spec_post))
          posts in
        (* eliminate those for which the symbolic execution does not go through *)
        let specs' = List.filter (fun (spec_pre, spec_post) -> 
          if Config.symb_debug()
          then begin
            Printf.printf "\nStarting symbolic execution for...\n";
            Format.printf "@\nSpec pre:@\n    %a@." string_inner_form spec_pre; 
            Format.printf "@\nSpec post:@\n    %a@." string_inner_form spec_post; 
          end;
          Hashtbl.clear formset_table;
          verify_inner mname stmts spec_pre spec_post symexec_lo abs_rules) specs in
        specs'
