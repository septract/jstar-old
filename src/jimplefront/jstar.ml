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


open Debug
open Format
open Jparsetree
open Jimple_global_types
open Psyntax

let program_file_name = ref ""
let logic_file_name = ref "logic"
let spec_file_name = ref "specs"
let absrules_file_name = ref "abs"

let set_logic_file_name n =
  logic_file_name := n

let set_spec_file_name n =
  spec_file_name := n

let set_absrules_file_name n =
  absrules_file_name := n


let set_program_file_name n =
  program_file_name := n ;
  Support_symex.file := Filename.basename n


let set_specs_template_mode () =
  Config.specs_template_mode := true

let set_dotty_flag () =
  Config.dotty_print := true

let set_grouped () =
  Symexec.set_group true

let set_eclipse () =
   Config.eclipse_ref := true

let arg_list = Config.args_default @
[
("-e", Arg.Unit(set_eclipse), "run in eclipse");
("-template", Arg.Unit(set_specs_template_mode ), "create empty specs template" );
("-f", Arg.String(set_program_file_name ), "program file name" );
("-l", Arg.String(set_logic_file_name ), "logic file name" );
("-s", Arg.String(set_spec_file_name ), "spec file name" );
("-g", Arg.Unit(set_grouped), "group abstraction nodes" );
("-a", Arg.String(set_absrules_file_name ), "abstraction rules file name" );
("-dot", Arg.Unit(set_dotty_flag ), "print heaps in dotty format for every node of cfg (default=false) " );
 ]


let parse_program () =
  if log log_phase then
    fprintf logf "@[<4>Parsing program@ %s.@." !program_file_name;
  let ch =
    try
      open_in !program_file_name
    with Sys_error s -> failwith s in
  let program = Jparser.file Jlexer.token (Lexing.from_channel ch) in
  if log log_phase then fprintf logf "@[<4>Parsed@ %s.@." !program_file_name;
  (* Replace specialinvokes of <init> after news with virtual invokes of <init>*)
  let program = program in
  let rec spec_to_virt x maps = match x with
    DOS_stm(Assign_stmt(x,New_simple_exp(y)),source_pos)::xs ->
      DOS_stm(Assign_stmt(x,New_simple_exp(y)),source_pos)::(spec_to_virt xs ((x,y)::maps))
  | DOS_stm(Invoke_stmt(Invoke_nostatic_exp(Special_invoke,b,(Method_signature (c1,c2,Identifier_name "<init>",c4)),d)),source_pos)
    ::xs
    when List.mem (Var_name b,Class_name c1) maps
    ->
      DOS_stm(Invoke_stmt(Invoke_nostatic_exp(Virtual_invoke,b,(Method_signature (c1,c2,Identifier_name "<init>",c4)),d)),source_pos)
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
  Arg.parse
      arg_list
      (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
      usage_msg;

  if !program_file_name="" then
     eprintf "Program file name not specified. Can't continue....\n %s \n" usage_msg
  else
     let program=parse_program () in
     if !logic_file_name="" && not !Config.specs_template_mode then
       eprintf "@\nLogic file name not specified. Can't continue....\n %s \n" usage_msg
     else if !spec_file_name="" && not !Config.specs_template_mode then
       eprintf "@\nSpecification file name not specified. Can't continue....\n %s \n" usage_msg
     else if !absrules_file_name="" && not !Config.specs_template_mode then
       eprintf "@\nAbstraction rules file name not specified. Can't continue....\n %s \n" usage_msg
     else if !Config.specs_template_mode then
       (if log log_phase then
         fprintf logf "@[<4>Creating empty specs template for class@ %s.@." !program_file_name;
       Mkspecs.print_specs_template program)
     else (
       let signals = (if Sys.os_type="Win32" then [] else [Sys.sigint; Sys.sigquit; Sys.sigterm]) in
       List.iter
	 (fun s ->  Sys.set_signal s (Sys.Signal_handle (fun x -> Symexec.pp_dotty_transition_system (); exit x)))
         signals;
       if !Config.smt_run then Smt.smt_init();
       (* Load abstract interpretation plugins *)
       List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;       

       let l1,l2,cn = Load_logic.load_logic !logic_file_name
       in
       let logic = {empty_logic with seq_rules=l1; rw_rules=l2; consdecl=cn} in

       let l1,l2,cn = Load_logic.load_abstractions !absrules_file_name in
       let abs_rules = {empty_logic with seq_rules=l1; rw_rules=l2; consdecl=cn} in

       let spec_list : (Spec_def.class_spec list) = Load.import_flatten
           Cli_utils.specs_dirs            
           !spec_file_name
           (Jparser.spec_file Jlexer.token) in

       let Jimple_global_types.JFile(_,_,class_name,_,_,_) = program in

       let logic = Javaspecs.augmented_logic_for_class class_name spec_list logic in
       let logic = Javaspecs.add_common_apf_predicate_rules spec_list logic in
       (* Axioms use the "subtype" and "objsubtype" relation - see jlogic.ml *)
       let logic = Javaspecs.add_subtype_and_objsubtype_rules spec_list logic in

       (* Exports clause treatment *)
       let (logic_with_where_pred_defs,implications) = Javaspecs.logic_and_implications_for_exports_verification class_name spec_list logic in
       if safe then
         Classverification.verify_exports_implications
             implications
             logic_with_where_pred_defs;
         (* Since where predicates are local to the exports clause, we discard them after exports clause verification *)
       let logic = Javaspecs.add_exported_implications_to_logic spec_list logic in
       if log log_logic then (
         fprintf
            logf
            "@[<2>Augmented logic sequent rules%a@."
            (pp_list Psyntax.pp_sequent_rule) logic.seq_rules);
       (* End of exports clause treatment *)

       (* Axioms clause treatment *)
       let axiom_map = Javaspecs.spec_file_to_axiom_map spec_list in
       let implications = Javaspecs.implications_for_axioms_verification class_name axiom_map in
       if safe then
         Classverification.verify_axioms_implications
            class_name
            program
            implications
            axiom_map
            logic;
       let logic = Javaspecs.add_axiom_implications_to_logic spec_list logic in
       (*let _ = Prover.pprint_sequent_rules logic in*)
       (* End of axioms clause treatment *)

       if log log_specs then (
         fprintf
            logf
            "@[<2>Specifications%a@."
            (pp_list Spec_def.pp_class_spec) spec_list);
       let (static_method_specs,dynamic_method_specs) =
         Javaspecs.spec_file_to_method_specs spec_list in

       if log log_phase then
         fprintf logf "@[Starting symbolic execution.@.";
       Classverification.verify_methods
           program
           static_method_specs
           dynamic_method_specs
           logic abs_rules;
       Symexec.pp_dotty_transition_system ())



let _ =
  System.set_signal_handlers ();
  let mf = {
    mark_open_tag = (function
      | "b" -> System.terminal_red (* bad *)
      | "g" -> System.terminal_green (* good *)
      | _ -> assert false);
    mark_close_tag = (fun _ -> System.terminal_white);
    print_open_tag = (fun _ -> ());
    print_close_tag = (fun _ -> ())} in
  set_formatter_tag_functions mf;
  pp_set_formatter_tag_functions err_formatter mf;
  set_tags true; pp_set_tags err_formatter true;
  try main ()
  with Failure s -> eprintf "@{<b>FAILED:@} %s@." s
