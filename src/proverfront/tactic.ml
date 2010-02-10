open System
open Global_types
open Prover_types




exception No_such_rule of string

(* Get first rule with matching name *)
let rec string_to_rule rules name = match rules with
	| [] -> raise (No_such_rule name)
	| ((_, _, rule_name, _, _) as rule)::rest ->
		if String.compare rule_name name = 0 then rule
		else string_to_rule rest name		
		
let rec build_tactical tactic_syntax rules = match tactic_syntax with
	| Rule_names rns -> Rules (List.map (string_to_rule rules) rns)
	| Repeat_spec ts -> Repeat (build_tactical ts rules)
	| IfMatch_spec (ts_if, ts_then, ts_else) -> 
		 let t_if = build_tactical ts_if rules in
		 let t_then = build_tactical ts_then rules in
		 let t_else = build_tactical ts_else rules in
			IfMatch (t_if, t_then, t_else)

let load_tactic filename (rules : sequent_rule list) =
	let l = string_of_file filename in 
 (* if !(Debug.debug_ref) then Printf.printf "Start parsing tactic in %s...\n" filename; *)
  let tactic_spec = Jparser.tactic_file Jlexer.token (Lexing.from_string l) in 
  let tactic = build_tactical tactic_spec rules in
(*  if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
  if !(Debug.debug_ref) then print_tactic tactic; *)
  tactic
