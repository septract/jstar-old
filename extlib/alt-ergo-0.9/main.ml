(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2009                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Why_ptree

let _ = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ -> print_endline "User wants me to stop."; exit 1))

open Lexing
open Format
open Options

module Time = struct

  open Unix
    
  let u = ref 0.0
    
  let start () = u:=(times()).tms_utime

  let get () = (times()).tms_utime -. !u

end

module Sat = Sat

let print_status fmt s = 
  fprintf fmt "%s@."
    ((function 
	| Smt_ast.Unsat -> "unsat" 
	| Smt_ast.Unknown -> "unknown"
	| Smt_ast.Sat  -> "unknown (sat)") s)

let process_decl (env,consistent) d =
  let satmode = !smtfile or !satmode in
  let loc = match d with 
      Why_typing.Assume(_,l,_) | Why_typing.PredDef(_,l) 
    | Why_typing.Query(_,_,_,l) -> l 
  in
  try
    match d with
	Why_typing.Assume(f,loc,mf) -> 
	  Sat.assume env 
	    {Sat.f=f;age=0;name=None;mf=mf;gf=false} , consistent

      |	Why_typing.PredDef(f,loc) -> 
	  Sat.pred_def env f , consistent

      | Why_typing.Query(n,f,lits,loc) -> 
	  if consistent then
	    begin
	      Sat.unsat env 
		{Sat.f=f;age=0;name=None;mf=true;gf=true} stopb ; 
	      if not satmode then Loc.report loc
	    end;
	  if satmode then printf "@{<C.F_Red>unsat@}@." 
	  else printf "@{<C.F_Green>Valid@} (%2.4f)@." (Time.get());
	  env , consistent
  with 
    | Sat.Sat -> 
	if not satmode then Loc.report loc;
	if satmode then printf "unknown (sat)@." 
	else printf "I don't know@."; 
	env , consistent
    | Sat.Unsat -> 
	if not satmode then 
	  (Loc.report loc; 
	   printf "Inconsistent assumption\n@.")
	else printf "unsat@.";
	env , false
    | Sat.I_dont_know -> 
	if not satmode then (Loc.report loc; printf "I don't know.\n@.")
	else printf "unknown@.";
	env , consistent

let main file = 
  let lb = from_channel cin in
  try
    let d , status =
      if !smtfile then begin
	let lb_prelude = 
          try
	    from_channel (open_in (Version.libdir^"/alt-ergo/smt_prelude.mlw"))
          with Sys_error _ -> from_channel (open_in "smt_prelude.mlw") in
	let lp = Why_parser.file Why_lexer.token lb_prelude in
        let bname,l,status = Smt_parser.benchmark Smt_lex.token lb in
	if verbose then printf "converting smt file : ";
        let l = List.flatten (List.map Smt_to_why.bench_to_why l) in
	if verbose then printf "done.@.";
	if parse_only then exit 0;
        Why_typing.file (lp@l) , status
      end
      else
	(let a = Why_parser.file Why_lexer.token lb in
	 if parse_only then exit 0;
         Why_typing.file a) , Smt_ast.Unknown
    in
    if file <> " stdin" then close_in cin;
    if type_only then exit 0;
    let split_pbs = 
      List.map
	(fun d -> 
	   if select > 0 then Pruning.split_and_prune select d 
	   else [List.map (fun f -> f,true) d]) d
    in
    List.iter
      (List.iter 
	 (fun d ->
	    ignore
	      (Queue.fold process_decl 
		 (Sat.empty,true) (Why_typing.make_cnf d))))
      split_pbs
  with
    | Why_lexer.Lexical_error s -> 
	Loc.report (lexeme_start_p lb, lexeme_end_p lb);
	printf "lexical error: %s\n@." s;
	exit 1
    | Parsing.Parse_error ->
	let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
	Loc.report loc;
        printf "syntax error\n@.";
	exit 1
    | Why_typing.Error(e,l) -> 
	Loc.report l; 
	printf "typing error: %a\n@." Why_typing.report e;
	exit 1

let _ = main !file
(*  try main ()
  with e -> printf "%s@." (Printexc.to_string e); exit 2*)




  

