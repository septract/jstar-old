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
  let usage_msg="Usage: -f <test_file_name> -l <logic_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  Debug.dump := Format.std_formatter;

  if !program_file_name="" then 
    Printf.printf "Test file name not specified. Can't continue....\n %s \n" usage_msg
  else if !logic_file_name="" then
    Printf.printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
  else 
    let logic = load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name in
    let s = System.string_of_file !program_file_name  in
    if !(Debug.debug_ref) then Printf.printf "Start parsing tests in %s...\n" !program_file_name;
    let test_list  = Jparser.test_file Jlexer.token (Lexing.from_string s) 
    in if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" !program_file_name;
    List.iter (
    fun test ->
      match test with 
    | Global_types.TImplication (heap1,heap2,result) ->
	(*Printf.printf "Check implication\n %s\n ===> \n %s\n" (Plogic.string_form heap1) (Plogic.string_form heap2);*)
	(match (Prover.check_implication logic (Rlogic.convert heap1) (Rlogic.convert heap2)), result with 
	  true,true | false,false -> ()
	| true,false -> Format.printf "Test failed! Unsound as proved @\n@ %a@\n@ ===> @\n%a@\n " 
	      Plogic.string_form heap1 
	      Plogic.string_form heap2
	| false,true -> Format.printf "Test@ failed!@ Could@ not@ prove@ @\n@ %a@\n ===> @\n%a@\n " 
	      Plogic.string_form heap1 
	      Plogic.string_form heap2
	);
	if !(Debug.debug_ref) then Prover.pprint_proof stdout
	  
    | Global_types.TFrame (heap1, heap2, result)  -> ()
(*	Printf.printf "Find frame for\n %s\n ===> \n %s\n" (Plogic.string_form heap1) (Plogic.string_form heap2);
	let x = Prover.check_implication_frame logic 
	    (Rlogic.convert heap1) (Rlogic.convert heap2) in 
	(match x with [] -> Printf.printf "Can't find frame!" | _ -> List.iter (fun form -> Printf.printf "Frame:\n %s\n" (Rlogic.string_ts_form (Rterm.rao_create ()) form)) x);
	Printf.printf "\n"*)
    | Global_types.TAbs (heap1,result)  -> ()
	(* let x = Prover.abs logic (Rlogic.convert heap1) in 
(*e	List.iter (fun form -> Printf.printf "Abstracts to %s\n" (Logic.string_form form)) x;*)
	Printf.printf "\n "*)
    | Global_types.TInconsistency (heap1,result) ->
	(match Prover.check_inconsistency logic (Rlogic.convert heap1), result with 
	  true, true 
	| false,false -> ()
	| true,false -> Format.printf "Test failed! Prover found@ %a@ inconsistent, test said consistent.\n" 
	      Plogic.string_form heap1
	| false,true -> Format.printf "Test failed! Prover could not prove@ %a@ inconsistent.\n" 
	      Plogic.string_form heap1
	);
	if !(Debug.debug_ref) then Prover.pprint_proof stdout
    | Global_types.TEqual (heap,arg1,arg2,result) -> ()
(*	if Prover.check_equal logic heap arg1 arg2 
	then Printf.printf("Equal!\n\n") else Printf.printf("Not equal!\n\n")*)
  )
      test_list


let _ = main ()
