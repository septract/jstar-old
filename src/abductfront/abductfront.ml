(********************************************************
   This file is part of jStar 
	src/symbfront/symbfront.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

(* This file is a front end to the symbolic execution *)

open List
open Printf
open Methdec_core
open Pprinter_core
open Load_logic

let question_file_name = ref "";;
let symexec_logic_file_name = ref "";;
let abduct_logic_file_name = ref "";;
let absrules_file_name = ref "";;

let proof_succes = ref true;; 

let set_question_name n =  question_file_name := n 
let set_symexec_logic_file_name n =  symexec_logic_file_name := n 
let set_abduct_logic_file_name n =  abduct_logic_file_name := n 
let set_absrules_file_name n =  absrules_file_name := n 

let arg_list = [ 
  ("-f", Arg.String(set_question_name ), "question file name" );
  ("-ls", Arg.String(set_symexec_logic_file_name ), "symbolic execution logic file name" );
  ("-la", Arg.String(set_abduct_logic_file_name ), "abduction logic file name" );
  ("-a", Arg.String(set_absrules_file_name ), "abstraction rules file name" );
]


let main () : unit = 
  let usage_msg=
"Usage: -ls <symexec_logic_file_name>  -la <abduct_logic_file_name>  -a <abstraction_file_name>  -f <question_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !question_file_name="" then 
    printf "Question file not specified. Can't continue....\n %s \n" usage_msg
  else if !symexec_logic_file_name="" then
    printf "Symbolic execution logic file name not specified. Can't continue....\n %s \n" usage_msg
  else if !abduct_logic_file_name="" then
    printf "Abduction logic file name not specified. Can't continue....\n %s \n" usage_msg
  else if !absrules_file_name="" then
    printf "Abstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
  else
    let l1,l2 = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !symexec_logic_file_name) in 
    let symexec_lo = l1,l2, Psyntax.default_pure_prover in
    let l1,l2 = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !abduct_logic_file_name) in 
    let abduct_lo = l1,l2, Psyntax.default_pure_prover in
    let l1,l2 = Load_logic.load_logic  (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !absrules_file_name in 
    let abs_rules = (l1,l2, Psyntax.default_pure_prover) in
    let question_list = System.parse_file Jparser.symb_question_file Jlexer.token !question_file_name "Question" true in
    List.iter (
    fun question ->
      match question with 
      
       | Specification(mname,spec,core)  ->
          Format.printf "\nMethod: %s\nSpec: %a"  mname  Spec.spec2str spec; 
       	  let stmts_core = map (fun x -> Methdec_core.stmt_create x [] []) core in 
          let specs = Abduction.bi_abduct mname stmts_core spec symexec_lo abduct_lo abs_rules in
          Format.printf "\nDiscovered specs:\n";
          List.iter (fun (spec_pre, spec_post) ->
            Format.printf "@\npre:@\n    %a@." Sepprover.string_inner_form spec_pre;
            Format.printf "@\npost:@\n    %a@." Sepprover.string_inner_form spec_post;)
            specs
          
       | _ -> Format.printf "Currently unsupported"
       
    ) question_list


let _ = main ()
