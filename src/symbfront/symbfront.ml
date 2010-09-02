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
open Psyntax

let question_file_name = ref "";;
let logic_file_name = ref "";;
let absrules_file_name = ref "";;

let arg_list = Config.args_default @ 
  [ 
("-f", Arg.Set_string(question_file_name ), "question file name" );
("-l", Arg.Set_string(logic_file_name ), "logic file name" );
("-a", Arg.Set_string(absrules_file_name ), "abstraction rules file name" );
  ]


let main () : unit = 
  let usage_msg=
"Usage: -l <logic_file_name>  -a <abstraction_file_name>  -f <question_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !question_file_name="" then 
    printf "Question file not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else if !absrules_file_name="" then
    printf "Abstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
  else
    if !Config.smt_run then Smt.smt_init !Config.solver_path; 

    let l1,l2,cn = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name) in 
    let lo = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let l1,l2,cn = Load_logic.load_logic  (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !absrules_file_name in 
    let abs_rules = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let question_list = System.parse_file Jparser.symb_question_file Jlexer.token !question_file_name "Question" true in
    List.iter (
    fun question ->
      match question with 
      
       | Specification(mname,spec,core)  ->
          Format.printf "Method: %s\nSpec: %a"  mname  Spec.spec2str spec; 
       	  let stmts_core = map (fun x -> Methdec_core.stmt_create x [] []) core in 
          if Symexec.verify mname stmts_core spec lo abs_rules then
          Format.printf "Good specification!\n\n" else Format.printf "Bad specification!\n\n" 
          
       | _ -> Format.printf "Currently unsupported"
       
    ) question_list

(*    List.iter (fun x -> pp_stmt_core Format.std_formatter x; 
	           Format.print_newline ())  core_list; *)



let _ = main ()
