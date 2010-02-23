open Load

type action =
	{
		ac_name : string;
		ac_action : unit -> unit
	}
	
let rules = ref []
let add_rules rule_list = rules := rule_list @ !rules	
let print_rules () = Format.printf "Rules:\n  [%a]\n\n@?" Prover_types.print_rule_list !rules

let rwm = ref Rterm.rm_empty
let add_rwm new_rwm =
	let add_rw r w = rwm := Rterm.rm_add r w !rwm in
	Rterm.RewriteMap.iter add_rw new_rwm

let tactics = ref []
let add_tactic tactic = tactics := !tactics@[tactic]

let active_tactic = ref None 
let set_active_tactic n = active_tactic := Some n
let clear_active_tactic = active_tactic := None

let print_tactics () =
	let mark n = if !active_tactic = Some n then "*" else " " in
	let rec print_tactics_inner n = function
		| [] -> ()
		| tc::tcs -> 
			Format.printf "%s %i: %a\n@?" (mark n) n Prover_types.print_tactical tc;
			print_tactics_inner (n+1) tcs
	in
	Format.print_string "Tactics:\n";
	print_tactics_inner 0 !tactics
		

let tests = ref []
let add_tests test_list = tests := test_list @ !tests	
(*let print_tests () = Format.printf "Tests:\n  [%a]\n@?" Prover_types.print_rule_list !rules*)

let rec input_choice min max choose () =
		let choice = read_int () in
		if choice < min or choice >= max
		then 
			(
				Format.printf "Choice must be between %i and %i@?" min max;
				input_choice min max choose ()
			)
		else
			choose choice	

let load_logic () =
	let logic_file_name =
		Format.printf "Name of logic file: @?";
		read_line ()
	in
	try
		let (rule_list, new_rwm) = load_logic_extra_rules (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") logic_file_name [] in
		add_rules rule_list;
		add_rwm new_rwm
	with Exit -> 		
		Format.printf "%s not found\n@?" logic_file_name;
		()

let load_test ()	=
	let test_file_name =
		Format.printf "Name of test file: @?";
		read_line ()
	in
	try
    let s = System.string_of_file test_file_name  in
    if true || !(Debug.debug_ref) then Format.printf "Start parsing tests in %s...@\n" test_file_name;
    let test_list  = Jparser.test_file Jlexer.token (Lexing.from_string s) 
    in if !(Debug.debug_ref) then Format.printf "Parsed %s!@\n" test_file_name;
		add_tests test_list
	with Exit ->
		Format.printf "%s not found\n@?" test_file_name;
		()

let input_tactic () =
	let tactic_string =
		Format.printf "Tactic: @?";
		read_line ()
	in
	let tactic_spec = Jparser.tactic_file Jlexer.token (Lexing.from_string tactic_string) in
	let tactic = Tactic.build_tactical tactic_spec !rules in
	add_tactic tactic

let choose_active_tactic () =
	input_choice 0 (List.length !tactics) set_active_tactic ()

let run_test logic test =
	match test with 
    | Global_types.TImplication (heap1,heap2,result) ->
			(*Format.printf "Check implication\n %s\n ===> \n %s\n" (Plogic.string_form heap1) (Plogic.string_form heap2);*)
			(match (Prover.check_implication logic (Rlogic.convert heap1) (Rlogic.convert heap2)), result with 
	  		true,true | false,false -> ()
			| true,false -> Format.printf "Test failed! Unsound as proved @\n@ %a@\n@ ===> @\n%a@\n " 
	      Plogic.string_form heap1 
	      Plogic.string_form heap2
			| false,true -> Format.printf "Test@ failed!@ Could@ not@ prove@ @\n@ %a@\n ===> @\n%a@\n " 
	      Plogic.string_form heap1 
	      Plogic.string_form heap2
			)
		(*	if !(Debug.debug_ref) then Prover.pprint_proof stdout*)	  
    | Global_types.TFrame (heap1, heap2, result)  -> 
			(*	Format.printf "Find frame for\n %s\n ===> \n %s\n" (Plogic.string_form heap1) (Plogic.string_form heap2);*)
			let x = Prover.check_implication_frame logic 
	    					(Rlogic.convert heap1) (Rlogic.convert heap2) in 
			if Prover.check_equiv x [(Rlogic.convert result)] then ()
			else (
	  		Format.printf "Incorrect frame for:@\n%a@\n ===> @\n%a@\n"
	      	Plogic.string_form heap1 
	      	Plogic.string_form heap2;
	  		List.iter 
	      	(fun form -> 
						Format.printf "Resulted in frames:@\n %a@\n" Rlogic.string_ts_form form) x;
	  		Format.printf "Was expecting:@\n%a@\n" Plogic.string_form result
	 		)
    | Global_types.TAbs (heap1,result)  ->
			let x = Prover.abs logic (Rlogic.convert heap1) in
			if Prover.check_equiv x [(Rlogic.convert result)] then ()
			else (
	  		Format.printf "Incorrect Abstraction for:@\n%a@\n "
	      	Plogic.string_form heap1;
	  		List.iter 
	      	(fun form -> 
						Format.printf "Resulted in forms:@\n %a@\n" Rlogic.string_ts_form form) x;
	  		Format.printf "Was expecting:@\n%a@\n" Plogic.string_form result
	 		)	
    | Global_types.TInconsistency (heap1,result) ->
			(match Prover.check_inconsistency logic (Rlogic.convert heap1), result with 
	  		true, true 
			| false,false -> ()
			| true,false -> Format.printf "Test failed! Prover found@ %a@ inconsistent, test said consistent.@\n" 
	      								Plogic.string_form heap1
			| false,true -> Format.printf "Test failed! Prover could not prove@ %a@ inconsistent.@\n" 
	      								Plogic.string_form heap1
			);
		(*	if !(Debug.debug_ref) then Prover.pprint_proof stdout*)
    | Global_types.TEqual (heap,arg1,arg2,result) -> ()
	(*	if Prover.check_equal logic heap arg1 arg2 
	then Format.printf("Equal!\n\n") else Format.printf("Not equal!\n\n")*)


exception Prompt_quit	
	
let actions =
	[
		{
			ac_name = "Quit";
			ac_action =
				fun () -> Format.print_string "Quitting...\n"; raise Prompt_quit
		};
		{
			ac_name = "Print rules";
			ac_action = print_rules
		};
		{
			ac_name = "Print tactics";
			ac_action = print_tactics
		};
		{
			ac_name = "Load logic from file";
			ac_action = load_logic
		};
		{
			ac_name = "Load tests from file";
			ac_action = load_test
		};
		{
			ac_name = "Input tactic";
			ac_action = input_tactic
		};
		{
			ac_name = "Choose active tactic";
			ac_action = choose_active_tactic
		};
		{
			ac_name = "Run all tests";
			ac_action = fun () -> 
				let tactic = match !active_tactic with
					| None -> Prover.default_tactical !rules
					| Some n -> List.nth !tactics n
				in
				let logic = (tactic, !rwm, Prover.default_pure_prover) in
				List.iter (run_test logic) !tests
		}
	]
	
let print_actions () =
	let print_action n ac = Format.printf "%i: %s\n@?" n ac.ac_name in
	let rec print_actions_inner n = function
		| [] -> ()
		| ac::acs -> print_action n ac; print_actions_inner (n+1) acs
	in
	print_actions_inner 0 actions

let choose_action =
	let choose choice = (List.nth actions choice).ac_action in
	input_choice 0 (List.length actions) choose

let rec main () =
	print_actions ();
	try
		choose_action () ();
		main ()
	with Prompt_quit -> ()

let _ = main ()
