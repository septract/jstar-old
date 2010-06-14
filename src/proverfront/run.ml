(********************************************************
   This file is part of jStar 
	src/proverfront/run.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
open Congruence
open Debug
open Format
open Load_logic

let _ = CC.test ()

let program_file_name = ref ""
let logic_file_name = ref ""
let verbose = ref false
 
let set_file_name n = 
  program_file_name := n 

let set_logic_file_name n = 
  logic_file_name := n 

let set_verbose_mode () =
  verbose := true

let arg_list =[ ("-f", Arg.String(set_file_name ), "program file name" );
		("-l", Arg.String(set_logic_file_name ), "logic file name" ); 
	        ("-v", Arg.Unit(set_verbose_mode), "Verbose proofs");]



let main () =
  let usage_msg="Usage: -f <file_name> -l <logic_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !program_file_name="" then 
    printf "File name not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else 
    let l1,l2 = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name) in 
    let logic = l1,l2, Psyntax.default_pure_prover in
(*    let s = System.string_of_file !program_file_name  in*)
    let question_list = System.parse_file Jparser.question_file Jlexer.token !program_file_name "Questions" in

    List.iter (
    fun question ->
      match question with 
    | Psyntax.Implication (heap1,heap2) ->
	printf "Check implication\n %a\n ===> \n %a\n" Psyntax.string_form heap1   Psyntax.string_form heap2;
	if (Sepprover.implies_opt logic (Sepprover.convert heap1) heap2)
	then printf("Holds!\n\n") else printf("Does not hold!\n\n");
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Frame (heap1, heap2)  -> 
	printf "Find frame for\n %a\n ===> \n %a\n" Psyntax.string_form heap1   Psyntax.string_form heap2;
	let x = Sepprover.frame_opt logic 
	    (Sepprover.convert heap1) heap2 in 
	(match x with None -> printf "Can't find frame!" | Some x -> List.iter (fun form -> printf "Frame:\n %a\n" Sepprover.string_inner_form  form) x);
	printf "\n";
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Abs (heap1)  ->
	printf "Abstract@\n  @[%a@]@\nresults in@\n  " Psyntax.string_form heap1;
	let x = Sepprover.abs_opt logic (Sepprover.convert heap1) in 
	List.iter (fun form -> printf "%a\n" Sepprover.string_inner_form form) x;
	printf "\n";
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Inconsistency (heap1) ->
	if Sepprover.inconsistent_opt logic (Sepprover.convert heap1) 
	then printf("Inconsistent!\n\n") else printf("Consistent!\n\n");
	if log log_prove then (
          fprintf logf "@[";
          Prover.pprint_proof logf;
          fprintf logf "@.")
    | Psyntax.Equal (heap,arg1,arg2) -> ()
(*	if Prover.check_equal logic heap arg1 arg2 
	then Printf.printf("Equal!\n\n") else Printf.printf("Not equal!\n\n")*) 
(*    | _ -> Printf.printf "Currently unsupported" *)
  )
      question_list

let _ = main ()
