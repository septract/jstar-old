(********************************************************
   This file is part of jStar 
	src/jimplefront/run_parser.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

open Jparsetree
open Jimple_global_types

let program_file_name = ref ""
let logic_file_name = ref ""
let spec_file_name = ref ""
let absrules_file_name = ref ""

let set_logic_file_name n = 
  logic_file_name := n 

let set_spec_file_name n = 
  spec_file_name := n 

let set_absrules_file_name n = 
  absrules_file_name := n 


let set_program_file_name n = 
  program_file_name := n ;
  Support_symex.file := n

let set_verbose () = 
  Config.verbose := true 

let set_quiet () =
  Config.sym_debug := false

let set_specs_template_mode () = 
  Config.specs_template_mode := true 

let set_dotty_flag () = 
  Config.dotty_print := true 

let set_grouped () =
  Symexec.set_group true

let arg_list =[ 
("-v", Arg.Unit(set_verbose ), "run in verbose mode" );
("-q", Arg.Unit(set_quiet ), "run in quiet mode" );
  ("-template", Arg.Unit(set_specs_template_mode ), "create empty specs template" );
("-f", Arg.String(set_program_file_name ), "program file name" );
("-l", Arg.String(set_logic_file_name ), "logic file name" );
("-s", Arg.String(set_spec_file_name ), "spec file name" );
("-g", Arg.Unit(set_grouped), "group abstraction nodes" );
("-a", Arg.String(set_absrules_file_name ), "abstraction rules file name" );
("-dot", Arg.Unit(set_dotty_flag ), "print heaps in dotty format for every node of cfg (default=false) " );
 ]


(*
let parse_one_class cname =
  let cname= !path_class_files ^ cname ^".jimple" in
  Printf.printf "Start parsing class file %s...\n" cname;
  let s = string_of_file cname  in
  let parsed_class_file  = Jparser.file Jlexer.token (Lexing.from_string s) 
  in Printf.printf "Parsing %s... done!\n" cname;
  Printf.printf "\n\n\n%s" (Pprinter.jimple_file2str parsed_class_file);
  parsed_class_file
*)



let parse_program () =
  if Config.symb_debug() then Printf.printf "Parsing program file  %s...\n" !program_file_name;
  let ch = open_in !program_file_name  in
  let program =Jparser.file Jlexer.token (Lexing.from_channel ch)
  in if Config.symb_debug() then Printf.printf "Program Parsing... done!\n";
  (* Replace specialinvokes of <init> after news with virtual invokes of <init>*)
  let program = program in 
  let rec spec_to_virt x maps = match x with 
    DOS_stm(Assign_stmt(x,New_simple_exp(y)))::xs -> 
      DOS_stm(Assign_stmt(x,New_simple_exp(y)))::(spec_to_virt xs ((x,y)::maps))  
  | DOS_stm(Invoke_stmt(Invoke_nostatic_exp(Special_invoke,b,(Method_signature (c1,c2,Identifier_name "<init>",c4)),d)))
    ::xs 
    when List.mem (Var_name b,Class_name c1) maps
    ->
      DOS_stm(Invoke_stmt(Invoke_nostatic_exp(Virtual_invoke,b,(Method_signature (c1,c2,Identifier_name "<init>",c4)),d)))
      ::(spec_to_virt xs (List.filter (fun x -> fst x <> Var_name b) maps))
    | x::xs -> x::(spec_to_virt xs maps)
    | [] -> [] in
  let spec_to_virt_helper x =
          match x with 
          Some (f,g) -> Some(spec_to_virt f [],g)
               |x -> x in
  match program with 
    JFile(a,b,c,d,e,f) -> 
      JFile(a,b,c,d,e,List.map 
	      (function 
		  Method (a,b,c,d,e,f,g,h,i) 
		  -> Method(a,b,c,d,e,spec_to_virt_helper f,List.map spec_to_virt_helper g,spec_to_virt_helper h,spec_to_virt_helper i)
		| x -> x) f )
 


let main () =
  let usage_msg="Usage: -l <logic_file_name>  -a <abstraction_file_name>  -s <spec_file_name>  -f <class_file_program>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;
  Debug.debug_ref:=!Config.verbose;

  if !program_file_name="" then
     Printf.printf "Program file name not specified. Can't continue....\n %s \n" usage_msg
  else 
     let program=parse_program () in
     if !logic_file_name="" && not !Config.specs_template_mode then
       Printf.printf "Logic file name not specified. Can't continue....\n %s \n" usage_msg
     else if !spec_file_name="" && not !Config.specs_template_mode then
       Printf.printf "Specification file name not specified. Can't continue....\n %s \n" usage_msg
     else if !absrules_file_name="" && not !Config.specs_template_mode then
       Printf.printf "Abstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
     else if  !Config.specs_template_mode then 
       (Printf.printf "\nCreating empty specs template for class  %s... \n" !program_file_name;
	Mkspecs.print_specs_template program
       )
     else (
       List.iter 
	 (fun s ->  Sys.set_signal s (Sys.Signal_handle (fun x -> Symexec.pp_dotty_transition_system (); exit x)))
	 [Sys.sigint; Sys.sigquit; Sys.sigterm];
       try 
	 let l1,l2 = Load_logic.load_logic  (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name
	 in 
	 let logic = (l1,l2,Psyntax.default_pure_prover) in 
	
	 let l1,l2 = Load_logic.load_logic  (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !absrules_file_name in 
	 let abs_rules = (l1,l2, Psyntax.default_pure_prover) in
	 
	 let spec_list : (Spec_def.class_spec list) = Load.import_flatten 
	     (System.getenv_dirlist "JSTAR_SPECS_LIBRARY")
	     !spec_file_name
	     (Jparser.spec_file Jlexer.token) in
			
	 let Jimple_global_types.JFile(_,_,class_name,_,_,_) = program in
	
	 let logic = Javaspecs.augmented_logic_for_class class_name spec_list logic in
	 let logic = Javaspecs.add_common_apf_predicate_rules spec_list logic in
	 (* Axioms use the "subtype" and "objsubtype" relation - see jlogic.ml *)
	 let logic = Javaspecs.add_subtype_and_objsubtype_rules spec_list logic in
	
	 (* Exports clause treatment *)
	 let (logic_with_where_pred_defs,implications) = Javaspecs.logic_and_implications_for_exports_verification class_name spec_list logic in
				(*Inspect the augmented logic as follows:*)
	 			(*let _ = Prover.pprint_sequent_rules logic_with_where_pred_defs in*)
	 let _ = Classverification.verify_exports_implications implications logic_with_where_pred_defs in
				(* Since where predicates are local to the exports clause, we discard them after exports clause verification *)
	 let logic = Javaspecs.add_exported_implications_to_logic spec_list logic in
	 			(*let _ = Prover.pprint_sequent_rules logic in*)
	 (* End of exports clause treatment *)
	
	 (* Axioms clause treatment *)
	 let axiom_map = Javaspecs.spec_file_to_axiom_map spec_list in
	 let implications = Javaspecs.implications_for_axioms_verification class_name axiom_map in
	 let _ = Classverification.verify_axioms_implications class_name program implications axiom_map logic in
	 let logic = Javaspecs.add_axiom_implications_to_logic spec_list logic in
	 (*let _ = Prover.pprint_sequent_rules logic in*)
	 (* End of axioms clause treatment *)
	
	 let (static_method_specs,dynamic_method_specs) = Javaspecs.spec_file_to_method_specs spec_list in
	 
	 if Config.symb_debug() then Printf.printf "\n\n Starting symbolic execution...";
	 Classverification.verify_methods program static_method_specs dynamic_method_specs logic abs_rules ;
	   (*Symexec.compute_fixed_point program apfmap logic abs_rules static_method_specs dynamic_method_specs*)
	 Symexec.pp_dotty_transition_system () 
       with Assert_failure (e,l,c) -> Printf.printf "Error!!! Assert failure %s line %d character %d\n" e l c
      )
     
       
let _ = main ()
