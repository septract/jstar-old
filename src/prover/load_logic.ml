(* File to read a logic file and its imports. *)
open Prover
open System
open Global_types

let load_logic dirs filename = 
  (* Converts a list of rules and imports into a logic *)
  let rec rule_list_to_logic filename rl (sl,rm) =
    let rel_dir = (Filename.dirname filename) in
    let rec rule_list_to_logic_inner rl (sl,rm) =
      let rl = expand_equiv_rules rl in 
      match rl with
	[] -> sl,rm
      | r :: rl -> let (sl,rm) = rule_list_to_logic_inner rl (sl,rm) in 
	match r with
	| Import(file) -> 
	    if !(Debug.debug_ref) then Printf.printf "Importing : %s\n" file;
	    load_logic_inner (rel_dir::dirs) file (sl,rm)
	| SeqRule(r) -> (r::sl,rm)
	| RewriteRule(r) -> 
	    (match r with 
	      (fn,a,b,c,d,e,f,g) -> (sl,Rterm.rm_add fn ((a,b,(c,d,e),f,g)::(try Rterm.rm_find fn rm with Not_found -> [])) rm))
	| EquivRule(r) -> assert false
    in 
    let sl,rm = rule_list_to_logic_inner rl (sl,rm) in
    sl,rm
(* Loads a file and all its imports *)
  and load_logic_inner dirs filename (sl,rm) = 
    let filename = 
      try 
	System.find_file_from_dirs dirs filename 
      with Not_found  ->  Format.printf "Cannot find logic file: %s@\n" filename; raise Exit
    in   
    let l = string_of_file filename in 
    if !(Debug.debug_ref) then Printf.printf "Start parsing logic in %s...\n" filename;
    let rule_list  = Jparser.rule_file Jlexer.token (Lexing.from_string l) in 
    let logic = rule_list_to_logic filename rule_list (sl,rm) in 
    if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
    logic in 
  let sl,rm = load_logic_inner dirs filename ([],Rterm.rm_empty) in 
  sl,rm,default_pure_prover
