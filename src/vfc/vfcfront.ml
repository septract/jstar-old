(* This file is a frontend to the vfc verifier *)

open VfcAST

let vfc_file_name = ref "";;
let spec_file_name = ref "";;

let arg_list = Config.args_default @ 
  [ ("-f", Arg.Set_string(vfc_file_name ), "vfc file name" );
    ("-s", Arg.Set_string(spec_file_name ), "spec file name" );
  ]

let main () : unit = 
  let usage_msg = "Usage: -f <vfc_file_name>  -s <spec_file_name>" in 
  Arg.parse arg_list (fun s ->()) usage_msg;

  if !vfc_file_name="" then 
    Printf.printf "Vfc file not specified. Can't continue....\n %s \n" usage_msg
  else if !spec_file_name="" then
    Printf.printf "Spec file name not specified. Can't continue....\n %s \n" usage_msg
  else
  begin
    if !Config.smt_run then Smt.smt_init();
    let vfc_file = open_in !vfc_file_name in 
    let lexbuf = Lexing.from_channel vfc_file in 
    let res = Vfcparse.program Vfclex.token lexbuf in 
    () 
  end

let _ = main ()
