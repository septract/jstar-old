(* File to read a logic file and its imports. *)
open Psyntax
open System
open Load

let load_logic_extra_rules dirs filename extra_rules =
  let fileentrys = import_flatten_extra_rules dirs filename extra_rules (Jparser.rule_file Jlexer.token) in  
  let rl = expand_equiv_rules fileentrys in 
  let sl,rm = 
    List.fold_left
      (fun (sl,rm) rule ->
	match rule with
	| SeqRule(r) -> 
	    if !(Debug.debug_ref) 
	    then 
	      Format.printf "Loaded rule:@\n%a@\n" 
		string_psr r; 
	    (r::sl,rm)
	| RewriteRule(r) -> 
	    (match r with 
	      (fn,a,b,(c,d,e),f,g) -> (sl,rm_add fn ((a,b,(c,d,e),f,g)::(try rm_find fn rm with Not_found -> [])) rm))
	| EquivRule(r) -> assert false
      ) ([], rm_empty) rl
  in
  (sl,rm)

let load_logic dirs filename : (sequent_rule list * rewrite_map)= load_logic_extra_rules dirs filename []
