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
SMT TODO list: 

- mark things that are constructors as such in the term structure; 
  at the moment they're treated as predicates. 
  
- get rid of some of the gratuatous calls to the Format module & 
  do all the sexp construction through string-catenation 
  
- check that the SMT has started correctly; at the moment this is 
  assumed and a fault is raised only when the prover tries to read 
  the SMT's output. 

*)

open Psyntax
open Clogic
open Cterm
open Congruence
open Unix
open List
open Smtsyntax

exception SMT_error of string
exception SMT_fatal_error

(*let Config.smt_run = ref true;; *)
let smt_fdepth = ref 0;; 
let smtout = ref Pervasives.stdin;; 
let smtin = ref Pervasives.stderr;;
let smterr = ref Pervasives.stdin;;

let smtout_lex = ref (Lexing.from_string "");; 


(* use z3 by default. Can be overridden by the -p command line option *)
(*let solver_path = ref "z3";;*)


let smt_init () : unit = 
  if Config.smt_debug() then Format.printf "Initialising SMT\n"; 
  (try Config.solver_path := Sys.getenv "JSTAR_SMT_PATH" with Not_found -> ()); 
  let path = !Config.solver_path in 
  let o, i, e = Unix.open_process_full path (environment()) in 
  smtout := o;  smtin := i;  smterr := e;
  smtout_lex := Lexing.from_channel !smtout; 
  Config.smt_run := true; 
  if Config.smt_debug() then Format.printf "SMT running...\n"


let smt_fatal_recover () : unit  = 
  Format.printf "\n@{<b>SMT ERROR:@} "; 
  Format.printf "Oh noes! The SMT solver died for some reason. This shouldn't happen.\n"; 
  if Config.smt_debug() then 
    begin
      Format.printf "Error report from the solver:\n";
      try while true do Format.printf "%s\n" (input_line !smterr) done
      with End_of_file -> ()
    end; 
  Format.printf "Turning off SMT for this example..."; 
  Unix.close_process_full (!smtout, !smtin, !smterr); 
  Format.printf "SMT off.\n"; 
  Format.print_flush(); 
  Config.smt_run := false 



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
     let (e, xs') = partition (eq x) xs in 
     let eqs = equiv_partition eq xs' in 
     (x::e) :: eqs
  | [] -> []


(* construct all (unordered) pairs of list elements *)
let rec list_to_pairs 
    (xs : 'a list) 
    : ('a * 'a) list = 
  match xs with 
  | x::xs -> (map (fun y -> (x,y)) xs) @ list_to_pairs xs
  | [] -> [] 


(* munge out input characters that make z3 die horribly *)
(* We should probably handle this in a more principled way *)

let cmd_munge (s : string) : string = 
  let s = Str.global_replace (Str.regexp "[@\$]") "AT_" s in
  s
  
let str_munge (s : string ) : string = 
  let s = Str.global_replace (Str.regexp "[<> @\*]")  "_" s in
  s


(* Datatype to hold smt type annotations *)

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


let smt_union_list (l : smttypeset list) : smttypeset = 
  fold_right SMTTypeSet.union l SMTTypeSet.empty        

let rec args_smttype (arg : Psyntax.args) : smttypeset = 
  match arg with
  | Arg_var v -> SMTTypeSet.singleton (SMT_Var(v)) 
  | Arg_string s -> 
          let rxp = (Str.regexp "^\(-?[0-9]+\)") in 
          if Str.string_match rxp s 0 then SMTTypeSet.empty 
          else SMTTypeSet.singleton (SMT_Op("string_const_"^(str_munge s), 0))

  | Arg_op ("builtin_plus",_) -> SMTTypeSet.empty
  | Arg_op ("builtin_minus",_) -> SMTTypeSet.empty
  | Arg_op ("builtin_mult",_) -> SMTTypeSet.empty

  | Arg_op (name, args) -> 
          let s = SMTTypeSet.singleton (SMT_Op(("op_"^name), (length args))) in 
          smt_union_list (s::(map args_smttype args))
  | Arg_cons (name, args) -> smt_union_list (map args_smttype args)
  | Arg_record fldlist -> SMTTypeSet.empty


(* Functions to convert various things to sexps & get types *)

let rec string_sexp_args (arg : Psyntax.args) : string = 
  match arg with 
  | Arg_var v -> Vars.string_var v
  | Arg_string s -> 
          let rxp = (Str.regexp "^\(-?[0-9]+\)") in 
          if Str.string_match rxp s 0 then (Str.matched_group 1 s)
          else "string_const_"^(str_munge s)
  
  | Arg_op ("builtin_plus",[a1;a2]) -> 
          Printf.sprintf "(+ %s %s)" (string_sexp_args a1) (string_sexp_args a2)
  | Arg_op ("builtin_minus",[a1;a2]) -> 
          Printf.sprintf "(- %s %s)" (string_sexp_args a1) (string_sexp_args a2)
  | Arg_op ("builtin_mult",[a1;a2]) -> 
          Printf.sprintf "(* %s %s)" (string_sexp_args a1) (string_sexp_args a2)

  | Arg_op (name,args) -> 
          Printf.sprintf "(%s %s)" ("op_"^name) (string_sexp_args_list args)
  | Arg_record _ -> ""  (* shouldn't happen as converted to preds *)
and string_sexp_args_list (argsl : Psyntax.args list) : string = 
  match argsl with 
  | [] -> ""
  | a::al -> (string_sexp_args a) ^ " " ^ (string_sexp_args_list al)


let string_sexp_eq (a : Psyntax.args * Psyntax.args) : string =
  match a with (a1, a2) -> 
  Printf.sprintf "(= %s %s)" (string_sexp_args a1) (string_sexp_args a2)


let string_sexp_neq (a : Psyntax.args * Psyntax.args) : string =
  match a with a1, a2 -> 
  Printf.sprintf "(distinct %s %s)" (string_sexp_args a1) (string_sexp_args a2)

  
let string_sexp_pred (p : string * Psyntax.args) : (string * smttypeset) = 
  match p with 
  | ("GT",(Arg_op ("tuple",[a1;a2]))) -> 
      (Printf.sprintf "(> %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | ("LT",(Arg_op ("tuple",[a1;a2]))) -> 
      (Printf.sprintf "(< %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | ("GE",(Arg_op ("tuple",[a1;a2]))) -> 
      (Printf.sprintf "(>= %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | ("LE",(Arg_op ("tuple",[a1;a2]))) -> 
      (Printf.sprintf "(<= %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)
      
  | (name, args) -> 
    let name = "pred_"^name in 
    match args with Arg_op ("tuple",al) ->
    let types = SMTTypeSet.add (SMT_Pred(name,(length al))) (args_smttype args) in 
    (Printf.sprintf "(%s %s)" name (string_sexp_args_list al), types)


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
  
  let eqneqs = (let a,b = split (eqs@neqs) in a@b) in 
  let eq_types = smt_union_list (map args_smttype eqneqs) in 
  
  let disj_list, disj_type_list = 
     split (map (fun (f1,f2) -> 
                  let f1s, f1v = string_sexp_form ts f1 in 
                  let f2s, f2v = string_sexp_form ts f2 in 
                  ( "(or " ^ f1s ^ " " ^ f2s ^ ")", 
                    SMTTypeSet.union f1v f2v ) ) form.disjuncts) in 
  let disj_sexp = String.concat " " disj_list in 
  let disj_types = smt_union_list disj_type_list in 
  
  let plain_list, plain_type_list = 
     split ( map string_sexp_pred
            ( RMSet.map_to_list form.plain 
            (fun (s,r) -> (s, get_pargs_norecs false ts [] r)))) in 
  let plain_sexp = String.concat " " plain_list in 

  let plain_types = smt_union_list plain_type_list in                     

  let types = smt_union_list [eq_types; disj_types; plain_types]in 

  let form_sexp = "(and true " ^ eq_sexp ^ " " ^ neq_sexp ^ " " ^ 
                                 disj_sexp ^ " " ^ plain_sexp ^ ")"  in
  (form_sexp, types) 


let string_sexp_decl (t : smt_type) : string = 
  match t with 
  | SMT_Var v -> Printf.sprintf "(declare-fun %s () Int)" (Vars.string_var v)
  | SMT_Pred (s,i) -> Printf.sprintf "(declare-fun %s (%s) Bool)" s (nstr "Int " i)
  | SMT_Op (s,i) -> Printf.sprintf "(declare-fun %s (%s) Int)" s (nstr "Int " i)
  

(* Main SMT IO functions *)
let smt_command 
    (cmd : string) 
    : smt_response = 
  try 
    let cmd = cmd_munge cmd in 
    if Config.smt_debug() then Format.printf "%s\n" cmd; 
    Format.print_flush(); 
    output_string !smtin cmd; 
    output_string !smtin "\n"; 
    flush !smtin; 
    let response = Smtparse.main Smtlex.token !smtout_lex in 
    Lexing.flush_input !smtout_lex; (* not sure why this is necessary *)
    match response with 
    | Error e -> raise (SMT_error e)
    | _ -> response
  with End_of_file -> raise SMT_fatal_error 


let smt_assert (ass : string) : unit =
  match smt_command ("(assert " ^ ass ^ " )") with 
  | Success -> ()
  | _ -> raise (SMT_error "Assertion failed!")


let smt_check_sat () : bool =
  match smt_command "(check-sat)" with 
  | Sat -> true
  | Unsat -> false
  | Unknown -> false


let smt_check_unsat () : bool =
  match smt_command "(check-sat)" with 
  | Unsat -> true
  | Sat -> false
  | Unknown -> false


let smt_push () : unit = 
  match smt_command "(push)" with 
  | Success -> smt_fdepth := (!smt_fdepth + 1) 
  | _ -> raise (SMT_error "Push failed!")

  
let smt_pop () : unit = 
  match smt_command "(pop)" with 
  | Success -> smt_fdepth := (!smt_fdepth - 1) 
  | _ -> raise (SMT_error "Pop failed!")


let smt_reset () : unit = 
  let rec do_n (n : int) (f : unit -> unit) : unit =
     match n with 
     | 0 -> () 
     | n -> f() ; do_n (n-1) f
  in 
  do_n !smt_fdepth smt_pop; 
  smt_fdepth := 0


(* Check whether two args are equal under the current assumptions *)
let smt_test_eq (a1 : Psyntax.args) (a2 : Psyntax.args) : bool = 
  smt_push(); 
  smt_assert (string_sexp_neq (a1,a2)); 
  let r = smt_check_unsat() in 
  smt_pop(); r 


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
    let query = "(not (=> (and true " ^ asm_eq_sexp ^ " " ^ asm_neq_sexp ^ " " ^ 
                                        asm_sexp ^ ") " ^ obl_sexp ^ "))" 
    in smt_assert query;    
                                      
    (* check whether the forumula is unsatisfiable *)
    let r = smt_check_unsat() in 
    smt_pop(); r 
  with 
  | SMT_error r -> 
    smt_reset(); 
    Format.printf "@{<b>SMT ERROR@}: %s\n" r; 
    Format.print_flush(); 
    false
  | SMT_fatal_error -> 
    smt_fatal_recover(); 
    false 
  

let true_sequent_smt (seq : sequent) : bool =  
  (Clogic.true_sequent seq)
    ||
  (* Call the SMT if the other check fails *)
  (if (not !Config.smt_run) then false 
  else 
  (if Config.smt_debug() 
   then Format.printf "Calling SMT to prove\n %a\n" Clogic.pp_sequent seq; 
   Clogic.plain seq.assumption 
    &&
   Clogic.plain seq.obligation 
    && 
   finish_him seq.ts seq.assumption seq.obligation))


let frame_sequent_smt (seq : sequent) : bool = 
  (seq.obligation = empty) 
    ||
  (if (not !Config.smt_run) then false 
  else 
  (if Config.smt_debug() 
   then Format.printf "Calling SMT to get frame from\n %a\n" Clogic.pp_sequent seq; 
   Clogic.plain seq.obligation
    && 
   finish_him seq.ts seq.assumption seq.obligation))



(* Update the congruence closure using the SMT solver *)
let ask_the_audience 
    (ts : term_structure)
    (form : formula)
    : term_structure = 
  if (not !Config.smt_run) then raise Backtrack.No_match 
  else try 
    if Config.smt_debug() then Format.printf "Calling SMT to update congruence closure\n"; 
  
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
  
    (* declare predicates *)
    SMTTypeSet.iter (fun x -> smt_command (string_sexp_decl x);()) types; 

    (* Assert the assumption *)                    
    let assm_query = "(and true " ^ ts_eq_sexp ^" "^ ts_neq_sexp ^" "^ form_sexp ^ ")"
    in smt_assert assm_query;    

    (* check for a contradiction *)
    if Config.smt_debug() then Format.printf "[Checking for contradiction in assumption]\n"; 
    if smt_check_unsat() then (smt_reset(); raise Assm_Contradiction);
    
    (* check whether there are any new equalities to find; otherwise raise Backtrack.No_match *)
    if Config.smt_debug() then Format.printf "[Checking for new equalities]\n"; 
    smt_push(); 
    let reps = get_args_rep ts in 
    let rep_sexps = String.concat " " (map (fun (x,y) -> string_sexp_neq (snd x,snd y)) 
                                                (list_to_pairs reps) )
    in 
    smt_assert ( "(and true " ^ rep_sexps ^ " )" ); 
    if smt_check_sat() then (smt_reset(); raise Backtrack.No_match); 
    smt_pop(); 

    (* Update the term structure using the new equalities *)  
    let req_equiv = map (map fst)
                        (equiv_partition (fun x y -> smt_test_eq (snd x) (snd y)) reps) 
    in 
    smt_pop();
    fold_left make_list_equal ts req_equiv
  with 
  | SMT_error r -> 
    smt_reset(); 
    Format.printf "@{<b>SMT ERROR@}: %s\n" r;
    Format.print_flush(); 
    raise Backtrack.No_match
  | SMT_fatal_error -> 
    smt_fatal_recover(); 
    raise Backtrack.No_match
  
