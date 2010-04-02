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

let method_name = ref "";;
let core_file_name = ref "";;
let spec_file_name = ref "";;
let logic_file_name = ref "";;
let absrules_file_name = ref "";;

let set_method_name n = method_name := n  
let set_core_name n =  core_file_name := n 
let set_spec n =  spec_file_name := n
let set_logic_file_name n =  logic_file_name := n 
let set_absrules_file_name n =  absrules_file_name := n 

let arg_list =[ 
  ("-m", Arg.String(set_method_name), "method name"); 
  ("-f", Arg.String(set_core_name ), "program file name" );
  ("-l", Arg.String(set_logic_file_name ), "logic file name" );
  ("-s", Arg.String(set_spec), "specification file name"); 
  ("-a", Arg.String(set_absrules_file_name ), "abstraction rules file name" );
]


let main () = 
  let usage_msg=
"Usage: -m <method_name>  -l <logic_file_name>  -a <abstraction_file_name>  
        -s <spec_file_name>  -f <core_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !core_file_name="" then 
    printf "Core file not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else if !absrules_file_name="" then
    printf "Abstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
  else if !spec_file_name="" then 
    printf "Specification file name not specified. Can't continue...\n %s \n" usage_msg
  else 
    let core_list = System.parse_file Jparser.core_file Jlexer.token !core_file_name "Core" true in
    let stmts_core = map (fun x -> Methdec_core.stmt_create x [] []) core_list in 
    let spec = System.parse_file Jparser.spec Jlexer.token !spec_file_name "Specification" true in
    let l1,l2 = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name) in 
      let lo = l1,l2, Psyntax.default_pure_prover in
	let l1,l2 = Load_logic.load_logic  (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !absrules_file_name in 
      let abs_rules = (l1,l2, Psyntax.default_pure_prover) in
	
	Symexec.verify !method_name stmts_core spec lo abs_rules 


let _ = main ()
