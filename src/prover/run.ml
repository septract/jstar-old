(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)
open Load_logic

let program_file_name = ref "";;
let logic_file_name = ref "";;
 
let set_file_name n = 
  program_file_name := n 

let set_logic_file_name n = 
  logic_file_name := n 

let f = Debug.debug_ref := false

let set_verbose_mode () =
  Debug.debug_ref := true

let arg_list =[ ("-f", Arg.String(set_file_name ), "program file name" );
		("-l", Arg.String(set_logic_file_name ), "logic file name" ); 
	        ("-v", Arg.Unit(set_verbose_mode), "Verbose proofs");]



let main () =
  let usage_msg="Usage: -f <file_name> -l <logic_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !program_file_name="" then 
    Printf.printf "File name not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    Printf.printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else 
    let logic = load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name in
(*    let s = System.string_of_file !program_file_name  in*)
    let question_list = System.parse_file Logic_parser.file Logic_lexer.token !program_file_name "Questions" true in

    List.iter (
    fun question ->
      match question with 
    | Prover.Implication (heap1,heap2) ->
	Format.printf "Check implication\n %a\n ===> \n %a\n" Plogic.string_form heap1   Plogic.string_form heap2;
	if (Prover.check_implication logic (Rlogic.convert heap1) (Rlogic.convert heap2))
	then Printf.printf("Holds!\n\n") else Printf.printf("Does not hold!\n\n")
    | Prover.Frame (heap1, heap2)  -> 
	Format.printf "Find frame for\n %a\n ===> \n %a\n" Plogic.string_form heap1   Plogic.string_form heap2;
	let x = Prover.check_implication_frame logic 
	    (Rlogic.convert heap1) (Rlogic.convert heap2) in 
	(match x with [] -> Printf.printf "Can't find frame!" | _ -> List.iter (fun form -> Format.printf "Frame:\n %a\n" (Rlogic.string_ts_form (Rterm.rao_create ())) form) x);
	Printf.printf "\n"
    | Prover.Abs (heap1)  ->
	Format.printf "Abstract@\n  @[%a@]@\nresults in@\n  " Plogic.string_form heap1;
	let x = Prover.abs logic (Rlogic.convert heap1) in 
	List.iter (fun form -> Format.printf "%a\n" (Rlogic.string_ts_form (Rterm.rao_create ())) form) x;
	Printf.printf "\n"
    | Prover.Inconsistency (heap1) ->
	if Prover.check_inconsistency logic (Rlogic.convert heap1) 
	then Printf.printf("Inconsistent!\n\n") else Printf.printf("Consistent!\n\n")
    | Prover.Equal (heap,arg1,arg2) -> ()
(*	if Prover.check_equal logic heap arg1 arg2 
	then Printf.printf("Equal!\n\n") else Printf.printf("Not equal!\n\n")*)
  )
      question_list

let _ = main ()
