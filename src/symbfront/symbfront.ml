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

open Methdec_core
open Pprinter_core

let program_file_name = ref "";;

let set_file_name n = 
  program_file_name := n 

let arg_list =[ ("-f", Arg.String(set_file_name ), "program file name" );]


let main () = 
  let usage_msg="Usage: -f <file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !program_file_name="" then 
    Printf.printf "File name not specified. Can't continue....\n %s \n" usage_msg
  else 
    let question_list = System.parse_file Jparser.core_file Jlexer.token !program_file_name "Questions" true in
	Printf.printf "parsing results:\n" ;
	List.map (pp_stmt_core Format.std_formatter) question_list;
    Printf.printf "Hello!\n"

let _ = main ()
