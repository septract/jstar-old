open Plogic
open Rlogic


type sequent_rule = psequent * (psequent list list) * string * ((* without *) pform * pform) * (where list)

let print_rule f ((_, _, name, _, _) : sequent_rule) = Format.printf "%s" name

let rec print_rule_list rules = function
	| [] -> ()
	| [rule] -> Format.printf "%a" print_rule rule
	| r::rs -> Format.printf "%a, %a" print_rule r print_rule_list rs


type tactical =
	| Rules of sequent_rule list                 (* try rules in order *)
	| Repeat of tactical                         (* repeat until fail *)
	| IfMatch of tactical * tactical * tactical  (* conditional *)

let rec print_tactical f = function
	| Rules rules -> Format.printf "[%a]" print_rule_list rules
	| Repeat t -> Format.printf "(%a)*" print_tactical t
	| IfMatch (t_if, t_then, t_else) ->
		Format.printf "<%a ? %a : %a>"
		  print_tactical t_if
			print_tactical t_then
			print_tactical t_else

let print_tactic t = Format.printf "Tactic: %a\n@?" print_tactical t
