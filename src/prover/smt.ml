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
 
(*
TODO list: 

- mark things that are constructors as such in the term structure; 
  at the moment they're treated as predicates. 
  
- parse responses from the smt correctly

*)

open Psyntax
open Clogic
open Cterm
open Congruence
open Unix
open List
open Backtrack
open Smtsyntax

exception SMT_error of string
exception SMT_fatal_error

let smt_run = ref true;; 
let smt_fdepth = ref 0;; 
let smtout = ref Pervasives.stdin;; 
let smtin = ref Pervasives.stderr;;
let smterr = ref Pervasives.stdin;;

let smtout_lex = ref (Lexing.from_string "");; 

let solver_path = ref "z3";;


let smt_init 
    (path : string) 
    : unit = 
  if !(Debug.debug_ref) then Format.printf "Initialising SMT\n"; 
  let o, i, e = Unix.open_process_full path (environment()) in 
  smtout := o;
  smtin := i;
  smterr := e;
  smtout_lex := Lexing.from_channel !smtout; 
  smt_run := true; 
  if !(Debug.debug_ref) then Format.printf "SMT running...\n"


let smt_fatal_recover () : unit  = 
  System.warning();
  Format.printf "Oh noes! The SMT solver died for some reason. This shouldn't happen.\n"; 
  Format.printf "Turning off the SMT for this example..."; 
  Unix.close_process_full (!smtout, !smtin, !smterr); 
  Format.printf "SMT off.\n"; 
  System.reset(); 
  Format.print_flush(); 
  smt_run := false 


(* Some helper functions *)

let rec unzipmerge xs = 
  match xs with 
  | [] -> []
  | ((a,b)::xs) -> a::b::(unzipmerge xs)


let unzip (xs : ('a * 'b) list) : ('a list * 'b list) = 
  fold_right (fun (e1,e2) (l1, l2) -> ((e1::l1),(e2::l2)) ) xs ([],[])
  

let rec do_n (n : int) (f : unit -> unit) : unit =
  match n with 
  | 0 -> () 
  | n -> f() ; do_n (n-1) f


(* concatenate n instances of string s *)
let rec nstr (s : string) (n : int) : string =
  match n with 
  | 0 -> ""
  | _ -> s^(nstr s (n-1))
  
  
(* Partition a list into sublists of equal elements *)
let rec equiv_partition
    (eq : 'a -> 'a -> bool) 
    (xs : 'a list)
    : 'a list list = 
  match xs with 
  | x::xs -> 
     let (e, xs') = List.partition (eq x) xs in 
     let eqs = equiv_partition eq xs' in 
     (x::e) :: eqs
  | [] -> []


(* construct all (unordered) pairs of list elements *)
let rec list_to_pairs 
    (xs : 'a list) 
    : ('a * 'a) list = 
  match xs with 
  | x::xs -> (List.map (fun y -> (x,y)) xs) @ list_to_pairs xs
  | [] -> [] 


(* munge out input characters that make z3 die horribly *)

let cmd_munge (s : string) : string = 
  let s = Str.global_replace (Str.regexp "@") "AT_" s in 
  let s = Str.global_replace (Str.regexp "\*") "STAR_" s in
  s
  
let str_munge (s : string ) : string = 
  let s = Str.global_replace (Str.regexp "[<> @\*]")  "_" s in 
  s

(* Datatype to hold smt type annotations (which btw are essentially guesses) *)

type smt_type = 
  | SMT_Var of Vars.var
  | SMT_Pred of string * int 
  | SMT_Op of string * int


module SMTTypeSet = 
  Set.Make(struct
    type t = smt_type
    let compare = compare
  end)
type smttypeset = SMTTypeSet.t


let make_smttype_pred (p : string * Psyntax.args) : smt_type = 
  match p with s, a -> 
  let name = String.concat "" ["pred_"; s] in 
  match a with Arg_op ("tuple",al) -> SMT_Pred(name,(length al))


let smt_union_list (l : smttypeset list) : smttypeset = 
  fold_right SMTTypeSet.union l SMTTypeSet.empty        

let rec args_smttype (arg : Psyntax.args) : smttypeset = 
  match arg with
  | Arg_var v -> SMTTypeSet.add (SMT_Var(v)) SMTTypeSet.empty
  | Arg_string s -> 
          let name = String.concat "" ["string_const_"; (str_munge s)] in 
          SMTTypeSet.add (SMT_Op(name, 0)) SMTTypeSet.empty
  | Arg_op ("builtin_plus",_) -> SMTTypeSet.empty
  | Arg_op (name, args) -> 
          let name = String.concat "" ["op_"; name] in 
          let s = SMTTypeSet.add (SMT_Op(name, (length args))) SMTTypeSet.empty in 
          smt_union_list (s::(List.map args_smttype args))
  | Arg_cons (name, args) -> 
          smt_union_list (List.map args_smttype args)
  | Arg_record fldlist -> SMTTypeSet.empty


(* Functions to convert various things to sexps & get types *)

let rec string_args_sexp ppf arg = 
  match arg with 
  | Arg_var v -> Format.fprintf ppf "%s" (Vars.string_var v)
  | Arg_string s -> 
          let name = String.concat "" ["string_const_"; (str_munge s)] in 
          Format.fprintf ppf "%s" name
  | Arg_op ("builtin_plus",[a1;a2]) -> Format.fprintf ppf "(+ %a %a)" string_args_sexp a1 string_args_sexp a2
(*  | Arg_op ("tuple",al) -> Format.fprintf ppf "(%a)" string_args_list al*)
  | Arg_op (name,args) -> 
          let name = String.concat "" ["op_"; name] in 
          Format.fprintf ppf "(%s %a)" name string_args_list_sexp args 
  | Arg_record _ -> Format.fprintf ppf "" 
and string_args_list_sexp ppf argsl = 
  match argsl with 
    [] -> Format.fprintf ppf ""
  | [a] -> Format.fprintf ppf "%a" string_args_sexp a
  | a::al -> Format.fprintf ppf "%a@ %a" string_args_sexp a string_args_list_sexp al


let string_sexp_eq (a : Psyntax.args * Psyntax.args) : string =
  match a with a1, a2 -> 
  Format.fprintf Format.str_formatter "(= %a %a)" 
                 string_args_sexp a1 string_args_sexp a2;
  Format.flush_str_formatter()


let string_sexp_neq (a : Psyntax.args * Psyntax.args) : string =
  match a with a1, a2 -> 
  Format.fprintf Format.str_formatter "(distinct %a %a)" 
                 string_args_sexp a1 string_args_sexp a2;
  Format.flush_str_formatter()

  
let string_sexp_pred (p : string * Psyntax.args) : (string * smttypeset)= 
  match p with s, a -> 
  let types = args_smttype a in 
  let types = SMTTypeSet.add (make_smttype_pred p) types in 
  match a with Arg_op ("tuple",al) ->
       Format.fprintf Format.str_formatter "(pred_%s %a)"
             s string_args_list_sexp al; 
       ( Format.flush_str_formatter(), types )
       


let rec string_sexp_form 
    (ts : term_structure)
    (form : formula) 
    : (string * smttypeset) = 
  (* Construct equalities and inequalities *)  
  let eqs = map (fun (a1,a2) -> ((get_pargs_norecs false ts [] a1),
                                   (get_pargs_norecs false ts [] a2))) form.eqs in 
  let neqs = map (fun (a1,a2) -> ((get_pargs_norecs false ts [] a1),
                                    (get_pargs_norecs false ts [] a2))) form.neqs in 
  let eq_sexp = String.concat " " (map string_sexp_eq eqs) in 
  let neq_sexp = String.concat " " (map string_sexp_eq neqs) in 
  
  let eq_types = smt_union_list (map args_smttype (unzipmerge (eqs@neqs))) 
  in 
  
  let disj_list, disj_type_list = 
     unzip (map (fun (f1,f2) -> 
                  let f1s, f1v = string_sexp_form ts f1 in 
                  let f2s, f2v = string_sexp_form ts f2 in 
                  ( String.concat "" ["(or "; f1s; f2s; ")"], 
                                    SMTTypeSet.union f1v f2v ) ) form.disjuncts) in 
  let disj_sexp = String.concat " " disj_list in 
  let disj_types = smt_union_list disj_type_list in 
  
  let plain_list, plain_type_list = 
     unzip ( map string_sexp_pred
            ( RMSet.map_to_list form.plain 
            (fun (s,r) -> (s, get_pargs_norecs false ts [] r)))) in 
  let plain_sexp = String.concat " " plain_list in 

  let plain_types = smt_union_list plain_type_list in                     

  let types = smt_union_list [eq_types; disj_types; plain_types]in 

  let form_sexp = String.concat " " [ "(and true "; 
                                      eq_sexp; neq_sexp; 
                                      disj_sexp; plain_sexp; ")" ]  in
  (form_sexp, types) 


let string_sexp_decl (t : smt_type) : string = 
  ( match t with 
    | SMT_Var v -> Format.fprintf Format.str_formatter 
                          "(declare-fun %s () Int)\n" 
                          (Vars.string_var v)
    | SMT_Pred (s,i) -> Format.fprintf Format.str_formatter
                          "(declare-fun %s (%s) Bool)" s (nstr "Int " i)
    | SMT_Op (s,i) -> Format.fprintf Format.str_formatter
                          "(declare-fun %s (%s) Int)" s (nstr "Int " i)
  ); 
  Format.flush_str_formatter()
  

(* Main SMT functions *)
let smt_command 
    (cmd : string) 
    : smt_response = 
  try 
    let cmd = cmd_munge cmd in 
    if !(Debug.debug_ref) then Format.printf "SMT command: %s\n" cmd; 
    output_string !smtin cmd; 
    output_string !smtin "\n"; 
    flush !smtin; 
    let response = Smtparse.main Smtlex.token !smtout_lex in 
    Lexing.flush_input !smtout_lex; 
    match response with 
    | Error e -> raise (SMT_error e)
    | _ -> response
  with End_of_file -> raise SMT_fatal_error 
  
     

let smt_push () : unit = 
  smt_command "(push)"; 
  smt_fdepth := (!smt_fdepth + 1)

  
let smt_pop () : unit = 
  smt_command "(pop)";
  smt_fdepth := (!smt_fdepth - 1) 


let smt_reset () : unit = 
  let n = !smt_fdepth in do_n n smt_pop


(* Check whether two args are equal under the current assumptions *)
let smt_test_eq (a1 : Psyntax.args) (a2 : Psyntax.args) : bool = 
  smt_push(); 
  let test_query = String.concat " " ["(assert"; string_sexp_neq (a1,a2); ")"] in 
  smt_command test_query; 
  let r = smt_command "(check-sat)" in 
  smt_pop(); 
  match r with 
  | Unsat -> (if !(Debug.debug_ref) then Format.printf "Found new equality\n"; true)
  | Sat -> false
    


(* try to establish that the pure parts of a sequent are valid using the SMT solver *)
let finish_him 
    (ts : term_structure)
    (asm : formula)
    (obl : formula)
    : bool = 
  try
    (* Push a frame to allow reuse of prover *)
    smt_push(); 
  
    (* Construct equalities and ineqalities from ts *)
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs_norecs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs_norecs ts) in 
    let asm_eq_sexp = String.concat " " (map string_sexp_eq eqs) in 
    let asm_neq_sexp = String.concat " " (map string_sexp_neq neqs) in
    
    let ts_types = smt_union_list (map args_smttype (get_args_all ts)) in 
    
    (* Construct sexps and types for assumption and obligation *)
    let asm_sexp, asm_types = string_sexp_form ts asm in 
    let obl_sexp, obl_types = string_sexp_form ts obl in
    
    let types = smt_union_list [ts_types; asm_types; obl_types] in 
    
    (* declare variables and predicates *)
    SMTTypeSet.iter (fun x -> smt_command (string_sexp_decl x);()) types; 

    (* Construct and run the query *)                    
    let query = String.concat " " [ "(assert (not (=> (and true "; 
                                      asm_eq_sexp; asm_neq_sexp; asm_sexp; ") "; 
                                      obl_sexp; 
                                     ")))"] 
    in                         
    smt_command query;    
                                      
    let r = smt_command "(check-sat)" in 
    smt_pop();
    (* check whether the forumula is unsatisfiable *)
    match r with 
    | Unsat -> true
    | Sat -> false
  with 
  | SMT_error r -> 
    smt_reset(); 
    System.warning(); Format.printf "SMT error: %s\n" r; System.reset(); 
    Format.print_flush(); 
    false
  | SMT_fatal_error -> 
    smt_fatal_recover(); 
    false 
  

let true_sequent_smt (seq : sequent) : bool =  
  (Clogic.true_sequent seq)
    ||
  (* Call the SMT if the other check fails *)
  (if (not !smt_run) then false 
  else 
  (if !(Debug.debug_ref) 
   then Format.printf "Calling SMT to prove\n %a\n" Clogic.pp_sequent seq; 
   Clogic.plain seq.assumption 
    &&
   Clogic.plain seq.obligation 
    && 
   finish_him seq.ts seq.assumption seq.obligation))


let frame_sequent_smt (seq : sequent) : bool = 
  (seq.obligation = empty) 
    ||
  (if (not !smt_run) then false 
  else 
  (if !(Debug.debug_ref) 
   then Format.printf "Calling SMT to get frame from\n %a\n" Clogic.pp_sequent seq; 
   Clogic.plain seq.obligation
    && 
   finish_him seq.ts seq.assumption seq.obligation))



(* Update the congruence closure using the SMT solver *)
let ask_the_audience 
    (ts : term_structure)
    (form : formula)
    : term_structure = 
  if (not !smt_run) then raise No_match 
  else try 
    if !(Debug.debug_ref) then Format.printf "[Calling SMT to update congruence closure]\n"; 
  
    smt_push(); 
    
    (* Construct equalities and ineqalities from ts *)
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs_norecs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs_norecs ts) in 
    let ts_eq_sexp = String.concat " " (map string_sexp_eq eqs) in 
    let ts_neq_sexp = String.concat " " (map string_sexp_neq neqs) in
  
    let ts_types = smt_union_list (map args_smttype (get_args_all ts)) in 
  
    (* Construct sexps and types for assumption and obligation *)
    let form_sexp, form_types = string_sexp_form ts form in 
  
    let types = smt_union_list [ts_types; form_types] in 
  
    (* declare  predicates *)
    SMTTypeSet.iter (fun x -> smt_command (string_sexp_decl x);()) types; 

    (* Assert the assumption *)                    
    let assm_query = String.concat " " [ "(assert (and true "; ts_eq_sexp; 
                                         ts_neq_sexp; form_sexp; ")) " ] 
    in smt_command assm_query;    

    (* check for a contradiction *)
    if !(Debug.debug_ref) then Format.printf "[Checking for contradiction in assumption]\n"; 
    match smt_command "(check-sat)" with 
    | Unsat -> (if !(Debug.debug_ref) then Format.printf "[SMT found contradiction in assumption]\n"; 
                smt_reset(); raise Assm_Contradiction)
    | Sat -> (); 

    (* check whether there are any new equalities to find; otherwise raise No_Match *)
    if !(Debug.debug_ref) then Format.printf "[Checking whether any new equalities exist]\n"; 
    smt_push(); 
    let reps = get_args_rep ts in 
    let rep_sexps = String.concat " " (List.map (fun (x,y) -> string_sexp_neq (snd x,snd y)) 
                                                (list_to_pairs reps) )
    in 
    smt_command (String.concat " " [ "(assert (and true "; rep_sexps; "))"]); 
    match smt_command "(check-sat)"  with 
    | Sat -> (smt_reset(); raise No_match) 
    | Unsat -> (); 
    smt_pop(); 

    (* Update the term structure using the new equalities *)  
    if !(Debug.debug_ref) then Format.printf "[Identifying new equalities]\n"; 
    let req_equiv = map (map fst)
                        (equiv_partition (fun x y -> smt_test_eq (snd x) (snd y)) reps) 
    in 
    smt_pop();
    fold_left make_list_equal ts req_equiv
  with 
  | SMT_error r -> 
    smt_reset(); 
    System.warning(); Format.printf "SMT error: %s\n" r; System.reset(); 
    Format.print_flush(); 
    raise No_match
  | SMT_fatal_error -> 
    smt_fatal_recover(); 
    raise No_match
  
