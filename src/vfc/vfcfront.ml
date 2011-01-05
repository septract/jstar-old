(* This file is a frontend to the VFC verifier *)

open VfcAST
open Psyntax

let vfc_file_name = ref "";;
let spec_file_name = ref "";;
let internal_spec_file_name = ref "vfc_specs";;
let logic_file_name = ref "vfc_logic";;
let absrules_file_name = ref "vfc_abs";;

let arg_list = Config.args_default @ 
  [ ("-f", Arg.Set_string (vfc_file_name), "vfc file name" );
    ("-s", Arg.Set_string (spec_file_name), "spec file name" );
  ]

let main () : unit = 
  let usage_msg = "Usage: -f <vfc_file_name>  -s <spec_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !vfc_file_name="" then 
    Printf.printf "Vfc file not specified. Can't continue...\n %s \n" usage_msg
  else if !spec_file_name="" then
    Printf.printf "Spec file name not specified. Can't continue...\n %s \n" usage_msg
  else
  begin
    if !Config.smt_run then Smt.smt_init();
    (* Load abstract interpretation plugins *)
    List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;
    
    let l1,l2,cn = Load_logic.load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !logic_file_name in 
    let lo = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let l1,l2,cn = Load_logic.load_logic (System.getenv_dirlist "JSTAR_LOGIC_LIBRARY") !absrules_file_name in 
    let abs_rules = {empty_logic with seq_rules = l1; rw_rules = l2; consdecl = cn} in
    let internal_specs = Jparser.vfc_spec_file Jlexer.token (Lexing.from_channel (open_in !internal_spec_file_name)) in 
    
    if Config.symb_debug() then Printf.printf "Vfc file parsing started...\n%!";
    let prog = Vfcparse.program Vfclex.token (Lexing.from_channel (open_in !vfc_file_name)) in
    if Config.symb_debug() then Printf.printf "\nVfc file successfully parsed...\n%!";
    if Config.symb_debug() then Printf.printf "Spec file parsing started...\n%!";
    let specs = Jparser.vfc_spec_file Jlexer.token (Lexing.from_channel (open_in !spec_file_name)) in 
    if Config.symb_debug() then Printf.printf "\nSpec file successfully parsed...\n%!";
    let file_prefix = String.sub !vfc_file_name 0 (String.index !vfc_file_name '.') in
    Vfc2core.verify file_prefix prog (internal_specs @ specs) lo abs_rules
  end

let _ = main ()
