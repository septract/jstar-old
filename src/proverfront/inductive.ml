(* File to read an inductive file (and later its imports). *)
open Prover
open System
open Global_types

let print_inductive_con inductive_con =
  let (heap, name, args) = inductive_con.con_def in
  Format.printf "\t%s: %a => %s\n" inductive_con.con_name Plogic.string_form heap name

let print_inductive inductive =
  Printf.printf "Inductive(%s):\n" inductive.ind_name;
  List.iter print_inductive_con inductive.ind_cons

let print_inddef = function
  | IndImport s -> Printf.printf "Import %s;\n" s
  | IndDef inductive -> print_inductive inductive

let print_inductive_rule = function
  | ImportEntry s -> Printf.printf "Import %s;\n" s
  | NormalEntry (SeqRule (_,_,name,_,_)) -> Printf.printf "Inductive rule: %s;\n" name
  | NormalEntry _ -> Printf.printf "Other rule;\n"

(*
let print_inductive_rule r = Printf.printf "Inductive rule\n%a\n" (Logic.string_rule r)
*)
let convert_inductive_con inductive_con =
  let (heap, name, args) = inductive_con.con_def in
  let premis = ([], [], heap) in
  let conc = ([], [], [Plogic.P_SPred (name, args)]) in
    SeqRule (conc, [[premis]], name^"_"^inductive_con.con_name, ([], []), [])

let convert_inductive inductive =
  let con_rules = List.map convert_inductive_con inductive.ind_cons in
  let collect_fresh_var l _ = (Pterm.Arg_var (Vars.freshp ()))::l in
  let fresh_args = List.fold_left collect_fresh_var [] inductive.ind_args in
  let extract_premise inductive_con = (* handle substituting equalitites *)
    let (heap, name, args) = inductive_con.con_def in
    let arg_eq cv v = Plogic.P_EQ (cv, v) in
    let arg_eqs = List.map2 arg_eq fresh_args args in
(*
    let collect_eq l v = (Plogic.P_EQ (Pterm.Arg_var (Vars.freshp ()), v))::l in
    let arg_eqs = List.fold_left collect_eq [] args in
*)
      ([], arg_eqs@heap, []) in
  let case_premises = List.map extract_premise inductive.ind_cons in
  let case_conc = ([], [Plogic.P_SPred (inductive.ind_name, fresh_args)], []) in
  let case_rule = SeqRule(case_conc, [case_premises], inductive.ind_name^"_case", ([], []), []) in
    case_rule::con_rules

let rec convert_inddefs = function
  | [] -> []
  | (IndImport s)::l -> (ImportEntry s)::(convert_inddefs l)
  | (IndDef inductive)::l -> 
      let inductive_rules = convert_inductive inductive in
      let inductive_entries = List.map (function r -> NormalEntry r) inductive_rules in
	inductive_entries@(convert_inddefs l)

let convert_inductive_file filename =
    let l = string_of_file filename in 
    if !(Debug.debug_ref) then Printf.printf "Start parsing inductive definitions in %s...\n" filename;
    let inductive_list  = Jparser.inductive_file Jlexer.token (Lexing.from_string l) in 
    let inductive_rules = convert_inddefs inductive_list in
    if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
    if !(Debug.debug_ref) then List.iter print_inddef inductive_list;
    if !(Debug.debug_ref) then List.iter print_inductive_rule inductive_rules;
    inductive_rules
