(********************************************************
   This file is part of jStar 
	src/parsing/load_logic.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
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
	    (sl,r::rm)
	| EquivRule(r) -> assert false
      ) ([], []) rl
  in
  (sl,rm)

let load_logic dirs filename : (sequent_rule list * rewrite_rule list)= load_logic_extra_rules dirs filename []
