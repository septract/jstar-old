(********************************************************
   This file is part of jStar
        src/symbfront/test_symb.ml
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
open Core
open Pprinter_core
open Load_logic
open Psyntax

let question_file_name = ref "";;
let logic_file_name = ref "";;
let absrules_file_name = ref "";;

let set_question_file_name fn =
  question_file_name := fn;
  Symexec.file := Filename.basename fn

let proof_succes = ref true;; 

let arg_list = Config.args_default @ 
  [ ("-f", Arg.String set_question_file_name, "question file name" );
  ("-l", Arg.Set_string logic_file_name, "logic file name" );
  ("-a", Arg.Set_string absrules_file_name, "abstraction rules file name" );
]


let main () : unit = 
  let usage_msg = "Usage: -l <logic_file_name>  -a <abstraction_file_name>  -f <question_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !question_file_name="" then 
    printf "Question file not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else if !absrules_file_name="" then
    printf "Abstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
  else
    if !Config.smt_run then Smt.smt_init(); 

    let l1,l2,cn = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name) in 
    let lo = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let l1,l2,cn = Load_logic.load_logic  (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !absrules_file_name in 
    let abs_rules = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in

    let question_list = 
      System.parse_file 
          Jparser.symb_test_file 
          Jlexer.token 
          !question_file_name 
          "Test" in
    List.iter (
    fun question ->
      match question with 
      | Core.SpecTest (mname,spec,core,result) ->
        let cfg = map Cfg_core.mk_node core in 
  	(match (Symexec.verify mname cfg spec lo abs_rules), result with 
  	  true,true | false,false -> Format.printf "."
  	| true,false -> Format.printf "Test failed!" 
  	| false,true -> Format.printf "Test failed!" 
  	)
    ) question_list



let _ = main ()
