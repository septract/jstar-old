(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2009                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

let fmt = Format.std_formatter
let _ = 
  Format.pp_set_tags fmt true;
  Print_color.add_to_format_tag fmt

let usage = "usage: alt-ergo [options] file.<mlw|smt>"

let type_only = ref false
let parse_only = ref false
let stopb = ref 8
let debug = ref false
let notriggers = ref false
let dcc = ref false
let duse = ref false
let duf = ref false
let dsat = ref false
let dsats = ref false
let dtyp = ref false
let dconstr = ref false
let dpairs = ref false
let verbose = ref false
let dfm = ref false
let dbitv = ref false
let dac = ref false
let dcp = ref false
let ddispatch = ref false
let options = ref false
let parse_only = ref false
let type_only = ref false
let tracefile = ref ""
let smtfile = ref false
let satmode = ref false
let bjmode = ref false
let glouton = ref false
let triggers_var = ref false
let redondance = ref 2
let astuce = ref false
let select = ref 0

let show_version () = Format.printf "Alt-Ergo %s@." Version.version; exit 0

let spec = [
  "-parse-only", Arg.Set parse_only , " stop after parsing";
  "-type-only", Arg.Set type_only , " stop after typing";
  "-notriggers", Arg.Set notriggers, "  trigger inference";
  "-debug", Arg.Set debug, "  sets the debugging flag";
  "-dcc", Arg.Set dcc, "  sets the debugging flag of cc";
  "-duse", Arg.Set duse, "  sets the debugging flag of use";
  "-duf", Arg.Set duf, "  sets the debugging flag of uf";
  "-dfm", Arg.Set dfm, "  sets the debugging flag of fm";
  "-dbitv", Arg.Set dbitv, "  sets the debugging flag of bitv";
  "-dac", Arg.Set dac, "  sets the debugging flag of ac";
  "-dcp", Arg.Set dcp, "  sets the debugging flag of critical pairs";
  "-dsat", Arg.Set dsat, "  sets the debugging flag of sat";
  "-dsats", Arg.Set dsats, "  sets the debugging flag of sat (simple output)";
  "-dtyp", Arg.Set dtyp, "  sets the debugging flag of typing";
  "-dconstr", Arg.Set dconstr, "  sets the debugging flag of constructors";
  "-dpairs", Arg.Set dpairs, "  sets the debugging flag of pairs";
   "-v", Arg.Set verbose, "  sets the verbose mode";
  "-version", Arg.Unit show_version, "  prints the version number";
  "-ddispatch", Arg.Set ddispatch, "  sets the debugging flag of sat";
  "-stop", Arg.Set_int stopb, " <n> set the stop bound";
  "-sat" , Arg.Set satmode , " mode sat/unsat";
  "-bj" , Arg.Set bjmode , " mode sat/unsat";
  "-glouton" , Arg.Set glouton, 
  " use ground terms in non-instanciated lemmas";
  "-redondance" , Arg.Set_int redondance, 
  " number of redondant (multi)triggers (2 by default)";
  "-select" , Arg.Set_int select, 
  "k tries to select relevant (at level k) hypotheses for each goal";
  "-triggers-var" , Arg.Set triggers_var , " allows variables as triggers";
  "-cctrace", Arg.Set_string tracefile, 
  " <file> set output file for cc trace ";
  "-astuce" , Arg.Set astuce, "";
  "-color" , 
  Arg.Unit (fun () -> Print_color.set_margin_with_term_width fmt;
              Print_color.disable false), "Set ainsi color in output"
]

let file = ref " stdin"
let cin =
  let ofile = ref None in
  let set_file s =
    if Filename.check_suffix s ".mlw" || Filename.check_suffix s ".why"
    then ofile := Some s
    else
      if Filename.check_suffix s ".smt"
      then begin 
	smtfile := true ; ofile := Some s
      end
      else raise (Arg.Bad "no .mlw or .smt extension");
  in
  Arg.parse spec set_file usage;
  match !ofile with Some f -> file := f ; open_in f 
    | None -> 	smtfile := true ; stdin

let type_only = ! type_only
let parse_only = ! parse_only
let stopb = !stopb
let notriggers = !notriggers
let debug = !debug
let debug_cc = !dcc
let debug_use = !duse
let debug_uf = !duf
let debug_fm = !dfm
let debug_bitv = !dbitv
let debug_ac   = !dac
let debug_cp   = !dcp
let debug_sat = !dsat
let debug_sat_simple = !dsats
let debug_typing = !dtyp
let debug_constr = !dconstr
let debug_pairs = !dpairs
let verbose = !verbose
let debug_dispatch = !ddispatch
let tracefile = !tracefile
let bjmode = !bjmode
let glouton = !glouton
let triggers_var = !triggers_var
let redondance = !redondance
let astuce = !astuce
let select = !select
