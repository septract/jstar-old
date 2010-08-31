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

let load_logic_extra_rules 
    dirs filename extra_rules 
    : (Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list) =
  let fileentrys = import_flatten_extra_rules dirs filename extra_rules (Jparser.rule_file Jlexer.token) in  
  let rl = expand_equiv_rules fileentrys in 
  let sl,rm,cn = 
    List.fold_left
      (fun (sl,rm,cn) rule ->
	match rule with
	| SeqRule(r) -> 
	    if Config.verb_proof() 
	    then 
	      Format.printf "Loaded rule:@\n%a@\n" 
		string_psr r; 
	    (r::sl,rm,cn)
	| RewriteRule(r) -> 
	    (sl,r::rm,cn)
	| ConsDecl(f) -> (sl,rm,f::cn) (* FIXME: put handler here *)
	| EquivRule(r) -> assert false
      ) ([], [], []) rl
  in
  (sl,rm,cn)

let load_logic 
    dirs filename 
    : (sequent_rule list * rewrite_rule list * string list) = 
  load_logic_extra_rules dirs filename []
