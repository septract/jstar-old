open System
open Global_types

type tactical =
	| Rules of Prover.sequent_rule list          (* try rules in order *)
	| Repeat of tactical                         (* repeat until fail *)
	| IfMatch of tactical * tactical * tactical  (* conditional *)

let print_rule f (_, _, name, _, _) = Format.printf "%s" name

let rec print_rule_list rules = function
	| [] -> ()
	| [rule] -> Format.printf "%a" print_rule rule
	| r::rs -> Format.printf "%a, %a" print_rule r print_rule_list rs

let rec print_tactical f = function
	| Rules rules -> Format.printf "[%a]" print_rule_list rules
	| Repeat t -> Format.printf "(%a)*" print_tactical t
	| IfMatch (t_if, t_then, t_else) ->
		Format.printf "<%a ? %a : %a>"
		  print_tactical t_if
			print_tactical t_then
			print_tactical t_else

let print_tactic t = Format.printf "Tactic: %a\n" print_tactical t

(* Running the prover with default_tactical rules *)
(* should be equivalent to running the old implementation *)
(* of the prover on rules *)
let default_tactical rules = Repeat (Rules rules)
let logic_to_default_tactical logic =
	let (rules, rwm, ep) = logic in default_tactical rules

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
			
let logic_to_tactical tactic_syntax logic =
	let (rules, rwm, ep) = logic in build_tactical tactic_syntax rules

let load_tactic filename logic =
	let l = string_of_file filename in 
  if !(Debug.debug_ref) then Printf.printf "Start parsing tactic in %s...\n" filename;
    let tactic_spec = Jparser.tactic_file Jlexer.token (Lexing.from_string l) in 
    let tactic = logic_to_tactical tactic_spec logic in
    if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
    if !(Debug.debug_ref) then print_tactic tactic;
    tactic
