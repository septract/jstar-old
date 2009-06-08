(* File to read a logic file and its imports. *)
open Prover

(* read a file into a string *)
let string_of_file fname =
  let ichan = if fname = "-" then stdin else open_in fname
  and str = String.create 1024
  and buf = Buffer.create 1024 in
  let rec loop () =
    let len = input ichan str 0 1024 in
    Buffer.add_substring buf str 0 len;
    if len = 0 then Buffer.contents buf else loop () in
  let s = loop () in
  close_in ichan;
  s


(* Converts a list of rules and imports into a logic *)
let rec rule_list_to_logic rl (sl,rm)  =
  let rec rule_list_to_logic_inner rl (sl,rm) =
    match rl with
      [] -> sl,rm
    | r :: rl -> let (sl,rm) = rule_list_to_logic_inner rl (sl,rm) in 
      match r with
      |	Import(file) -> load_logic file (sl,rm)
      | SeqRule(r) -> (r::sl,rm)
      | RewriteRule(r) -> 
	  (match r with 
	    (fn,a,b,c,d,e,f) -> (sl,Rterm.rm_add fn ((a,b,(c,d,e),f)::(try Rterm.rm_find fn rm with Not_found -> [])) rm))
  in 
  let sl,rm = rule_list_to_logic_inner rl (sl,rm) in
  sl,rm
(* Loads a file and all its imports *)
and load_logic filename (sl,rm) = 
    let l = string_of_file filename in 
    if !(Debug.debug_ref) then Printf.printf "Start parsing logic in %s...\n" filename;
    let rule_list  = Logic_parser.rule_file Logic_lexer.token (Lexing.from_string l) in 
    let logic = rule_list_to_logic rule_list (sl,rm) in 
    if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
    logic

let load_logic filename = 
  let sl,rm = load_logic filename  ([],Rterm.rm_empty) in 
  sl,rm,default_pure_prover
