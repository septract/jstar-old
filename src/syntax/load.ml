(* File to read a logic file and its imports. *)
open Prover
open System
open Global_types

let import_flatten dirs filename fileparser= 
  let rec import_flatten_inner dirs filename acc = 
    let rel_dir = (Filename.dirname filename) in
    let filename = 
      try 
	System.find_file_from_dirs dirs filename 
      with Not_found  ->  Format.printf "Cannot find file: %s@\n" filename; raise Exit
    in   
    if !(Debug.debug_ref) then Printf.printf "Start parsing logic in %s...\n" filename;
    let inchan = open_in filename in 
    let file_entry_list  = fileparser (Lexing.from_channel inchan) in 
    close_in inchan;
    if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
    List.fold_left
      (fun acc entry -> 
	match entry with 
	  ImportEntry filen -> 
	    import_flatten_inner (rel_dir::dirs) filen acc  
	| NormalEntry ent -> 
	    ent::acc	    
      ) acc file_entry_list 
  in
  import_flatten_inner dirs filename []

let load_logic dirs filename =
  let fileentrys = import_flatten dirs filename (Jparser.rule_file Jlexer.token) in  
  let rl = expand_equiv_rules fileentrys in 
  let sl,rm = 
    List.fold_left
      (fun (sl,rm) rule ->
	match rule with
	| SeqRule(r) -> (r::sl,rm)
	| RewriteRule(r) -> 
	    (match r with 
	      (fn,a,b,c,d,e,f,g) -> (sl,Rterm.rm_add fn ((a,b,(c,d,e),f,g)::(try Rterm.rm_find fn rm with Not_found -> [])) rm))
	| EquivRule(r) -> assert false
      ) ([],Rterm.rm_empty) rl
  in
  (sl,rm,default_pure_prover)
