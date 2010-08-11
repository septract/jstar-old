(********************************************************
   This file is part of jStar 
	src/prover/smt.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

open Psyntax
open Clogic
open Cterm
open Congruence
open Unix
open List

let readme, writeme = Unix.pipe ()

let solver_path="/Users/md466/bin/z3"

let smtout, smtin = Unix.open_process solver_path

exception SMT_error of string

let rec unzipmerge xs = 
  match xs with 
    [] -> []
  | ((a,b)::xs) -> a::b::(unzipmerge xs)
  


let nub (l : 'a list) : 'a list = 
  List.fold_right (fun e ls -> if List.mem e ls then ls else e :: ls) l []


(* let call_smt_stupid : Unit = 
    Format.printf "Calling SMT...\n" ; 
  flush Pervasives.stdout;
  let oc_in, oc_out = Unix.open_process solver_path in 
  let s = input_line Pervasives.stdin in 
  output_string oc_out s ;
  output_string oc_out "(exit)\n" ;
  flush oc_out ;
  let r = String.create 250 in
  let n = input oc_in r 0 250 in 
  print_string (String.sub r 0 n) ;
  print_string "Quitting SMT...\n";
  flush Pervasives.stdout ;
  Unix.close_process (oc_in, oc_out) *)

let dump_ts_eqs 
    (ts : term_structure) 
    (oeq : (Cterm.representative * Cterm.representative) list) 
    (oneq : (Cterm.representative * Cterm.representative) list) 
    : unit = 
  let eqs = get_eqs ts in
  let neqs = get_neqs ts in 
  let oeqs = map (fun (a1,a2) -> ((get_pargs false ts [] a1),
                                 (get_pargs false ts [] a2))) oeq in 
  let oneqs = map (fun (a1,a2) -> ((get_pargs false ts [] a1),
                                  (get_pargs false ts [] a2))) oneq in 
  let vars = nub (flatten ( map (fun x -> (flatten (map get_vars (unzipmerge x))))
                                      [ eqs; neqs; oeqs; oneqs ] )) in 
                           
  Format.printf "Variable declarations:\n";
  iter ( fun v -> Format.printf "(declare-fun %s () Int)\n" (Vars.string_var v) ) vars; 

  Format.printf "Assumptions:\n";
  iter ( fun (a1, a2) -> 
    if (a1 != a2) then 
      Format.printf "(= %a %a)\n" Psyntax.string_args_sexp a1 Psyntax.string_args_sexp a2
  ) eqs; 
  iter ( fun (a1, a2) -> 
    Format.printf "(distinct %a %a)\n" Psyntax.string_args_sexp a1 Psyntax.string_args_sexp a2
  ) neqs;
  
  Format.printf "Obligations:\n";
  
  iter (
    fun (a1, a2) -> 
    Format.printf "(= %a %a)\n" Psyntax.string_args_sexp a1 Psyntax.string_args_sexp a2
  ) oeqs;
  iter (
    fun (a1, a2) -> 
    Format.printf "(distinct %a %a)\n" Psyntax.string_args_sexp a1 Psyntax.string_args_sexp a2
  ) oneqs


let string_sexp_eq (a : Psyntax.args * Psyntax.args) : string =
  match a with a1, a2 -> 
  Format.fprintf Format.str_formatter "(= %a %a)" 
                 Psyntax.string_args_sexp a1 
                 Psyntax.string_args_sexp a2;
  Format.flush_str_formatter()


let string_sexp_neq (a : Psyntax.args * Psyntax.args) : string =
  match a with a1, a2 -> 
  Format.fprintf Format.str_formatter "(distinct %a %a)" 
                 Psyntax.string_args_sexp a1 
                 Psyntax.string_args_sexp a2;
  Format.flush_str_formatter()


let string_sexp_vdecl (v : Vars.var) : string = 
  Format.fprintf Format.str_formatter "(declare-fun %s () Int)\n" (Vars.string_var v); 
  Format.flush_str_formatter()


let smt_command 
    (cmd : string) 
    : string = 
  print_string "SMT command: "; print_string cmd; print_newline ();
  output_string smtin cmd; 
  output_string smtin "\n"; 
  flush smtin; 
  let r = (input_line smtout) in
  print_string "Result: "; print_string r; print_newline(); 
  if (String.length r >= 6) && (String.sub r 0 6) = "(error" then 
    raise (SMT_error r)
  else r  


let finish_him 
    (ts : term_structure)
    (oeq : (Cterm.representative * Cterm.representative) list) 
    (oneq : (Cterm.representative * Cterm.representative) list) 
    : bool = 
  try 
    (* Push a frame to allow deletion of context *)
    smt_command "(push)"; 
  
    (* Construct equalities and ineqalities from ts *)
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs ts) in 
    let asm_eq_sexp = String.concat " " (map string_sexp_eq eqs) in 
    let asm_neq_sexp = String.concat " " (map string_sexp_neq neqs) in 
  

    (* Construct equalities and inequalities from obligation *)  
    (* TODO: define recursively *)
    let oeqs = map (fun (a1,a2) -> ((get_pargs false ts [] a1),
                                   (get_pargs false ts [] a2))) oeq in 
    let oneqs = map (fun (a1,a2) -> ((get_pargs false ts [] a1),
                                    (get_pargs false ts [] a2))) oneq in 
    let obl_eq_sexp = String.concat " " (map string_sexp_eq oeqs) in 
    let obl_neq_sexp = String.concat " " (map string_sexp_eq oneqs) in 
    

    (* Construct variable declarations *)                                  
    let vars = nub (flatten ( map (fun x -> (flatten (map get_vars (unzipmerge x))))
                                      [ eqs; neqs; oeqs; oneqs ] )) in
    iter (fun v -> smt_command (string_sexp_vdecl v); () ) vars; 
      

    (* Construct and run the query *)                    
    let query = String.concat " " [ "(assert (not (=> (and "; 
                                  asm_eq_sexp; 
                                  asm_neq_sexp; 
                                  ") (and "; 
                                  obl_eq_sexp; 
                                  obl_neq_sexp; 
                                  "))))"] 
    in                         
    smt_command query;    
                                      
    let r = smt_command "(check-sat)" in 
    (*print_string r; print_newline() ;*)
    smt_command "(pop)";
    (String.length r >= 5) && (String.sub r 0 5) = "unsat"
  with SMT_error r -> 
    Printf.printf "\n"; 
    System.warning(); Printf.printf "SMT error: %s" r; System.reset(); 
    false
  

  
(*  let r = String.create 250 in
  let n = input smtout r 0 250 in 
  print_string (String.sub r 0 n); 
  flush Pervasives.stdout;
  false *)

let is_true_smt 
     (ts : term_structure) 
     (asm : formula) 
     (obl : formula)
     : bool = 
  obl.spat = RMSet.empty && 
  (* First try to avoid calling the SMT *)
  (( obl.plain = RMSet.empty && 
     obl.disjuncts = [] && 
     obl.eqs = [] && 
     obl.neqs = [] )
     ||
  (* Call the SMT if the other check fails *)
  finish_him ts obl.eqs obl.neqs )
  


let true_sequent_pimp seq  =  
   (seq.obligation.spat = RMSet.empty)
   && 
   (is_true_smt seq.ts seq.assumption seq.obligation)


