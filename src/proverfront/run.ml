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
open Load_logic

let _ = CC.test ()

let program_file_name = ref "";;
let logic_file_name = ref "";;

let f = Debug.debug_ref := false

let arg_list =[ ("-f", Arg.Set_string(program_file_name), "program file name");
		("-l", Arg.Set_string(logic_file_name), "logic file name"); 
	        ("-v", Arg.Set(Debug.debug_ref), "Verbose proofs");
	        ("-nosmt", Arg.Clear(Smt.smt_run),"Don't use the SMT solver");
	        ("-p", Arg.Set_string(Smt.solver_path), "SMT solver path"); ]


let main () =
  let usage_msg="Usage: -f <file_name> -l <logic_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !program_file_name="" then 
    Format.printf "File name not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    Format.printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else 
    if !Smt.smt_run then Smt.smt_init !Smt.solver_path; 

    let l1,l2 = (load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name) in 
    let logic = l1,l2, Psyntax.default_pure_prover in
    let s = System.string_of_file !program_file_name  in
    let question_list = System.parse_file Jparser.question_file Jlexer.token !program_file_name "Questions" true in

    List.iter (
    fun question ->
      match question with 
    | Psyntax.Implication (heap1,heap2) ->
	Format.printf "Check implication\n %a\n ===> \n %a\n" Psyntax.string_form heap1   Psyntax.string_form heap2;
	if (Sepprover.implies_opt logic (Sepprover.convert heap1) heap2)
	then Format.printf("Holds!\n\n") else Format.printf("Does not hold!\n\n");
	if !(Debug.debug_ref) then Prover.pprint_proof stdout
    | Psyntax.Frame (heap1, heap2)  -> 
	Format.printf "Find frame for\n %a\n ===> \n %a\n" Psyntax.string_form heap1   Psyntax.string_form heap2;
	let x = Sepprover.frame_opt logic 
	    (Sepprover.convert heap1) heap2 in 
	(match x with None -> Format.printf "Can't find frame!" | Some x -> List.iter (fun form -> Format.printf "Frame:\n %a\n" Sepprover.string_inner_form  form) x);
	Format.printf "\n";
	if !(Debug.debug_ref) then Prover.pprint_proof stdout
    | Psyntax.Abs (heap1)  ->
	Format.printf "Abstract@\n  @[%a@]@\nresults in@\n  " Psyntax.string_form heap1;
	let x = Sepprover.abs_opt logic (Sepprover.convert heap1) in 
	List.iter (fun form -> Format.printf "%a\n" Sepprover.string_inner_form form) x;
	Format.printf "\n";
	if !(Debug.debug_ref) then Prover.pprint_proof stdout
    | Psyntax.Inconsistency (heap1) ->
	if Sepprover.inconsistent_opt logic (Sepprover.convert heap1) 
	then Format.printf("Inconsistent!\n\n") else Format.printf("Consistent!\n\n");
	if !(Debug.debug_ref) then Prover.pprint_proof stdout
    | Psyntax.Equal (heap,arg1,arg2) -> ()
(*	if Prover.check_equal logic heap arg1 arg2 
	then Format.printf("Equal!\n\n") else Format.printf("Not equal!\n\n")*) 
    | _ -> Format.printf "Currently unsupported"
  )
      question_list

let _ = main ()
