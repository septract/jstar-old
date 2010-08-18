(********************************************************
   This file is part of jStar 
	src/prover/prover.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)


open Cterm
open Clogic
open Vars
open Misc
open Debug
open Psyntax
open Backtrack
open Smt


let prover_counter_example : Clogic.sequent list ref = ref []
let print_counter_example ()  = 
  Format.printf "Needed to prove:@   @[%a@]@\n@\n"
    (Debug.list_format "\nor" Clogic.pp_sequent)
    !prover_counter_example

let pprint_counter_example ppf () = 
  Format.fprintf ppf "Needed to prove:@   @[%a@]@\n@\n"
    (Debug.list_format "\nor" Clogic.pp_sequent)
    !prover_counter_example


let pprint_proof chan = 
  let s = Buffer.contents buffer_dump in 
  output_string chan s

let string_of_proof () =
  Buffer.contents buffer_dump

exception Failed_eg of Clogic.sequent list


let rec apply_rule_list_once 
   (rules : sequent_rule list) 
   (seq : Clogic.sequent) 
   ep 
   : Clogic.sequent list list
   =
  match rules with 
    [] -> raise No_match
  | rule::rules ->
      try 
	Clogic.apply_rule (Clogic.convert_rule rule) seq (*ep*)
      with 
      | No_match -> apply_rule_list_once rules seq ep


let rec sequents_backtrack 
    f (seqss : Clogic.sequent list list) xs 
    : Clogic.sequent list =
  match seqss with 
    [] -> raise (Failed_eg xs)
  | seqs::seqss -> 
      try f seqs 
      with 
	Failed ->  
	  Format.fprintf !dump "Backtracking!@\n"; sequents_backtrack f seqss xs
      | Failed_eg x -> 
	  Format.fprintf !dump "Backtracking!@\n"; sequents_backtrack f seqss (x @ xs)

let apply_rule_list 
    logic 
    (sequents : Clogic.sequent list) 
    (must_finish : Clogic.sequent -> bool) 
    (may_finish : Clogic.sequent -> bool) 
    : Clogic.sequent list 
    =
(* Clear pretty print buffer *)
  Buffer.clear buffer_dump;
  let rules,rwm,ep = logic in 
  let n = 0 in
  if true || !(Debug.debug_ref) then
    (List.iter (fun seq -> Format.fprintf !dump "Goal@ %a@\n@\n" Clogic.pp_sequent seq) sequents;
     Format.fprintf !dump "Start time :%f @\n" (Sys.time ()));
  let rec apply_rule_list_inner sequents n : Clogic.sequent list = 
    let search seqss : Clogic.sequent list = 
      sequents_backtrack 
	(fun seqs->apply_rule_list_inner seqs (n+1)) seqss [] in
    let sequents = map_option (Clogic.simplify_sequent rwm) sequents in 
  (* Apply rules lots *)
    List.flatten 
      (List.map 
	 (fun seq ->
	   Format.fprintf !dump "%s>@[%a@]@\n@." (String.make n '-') Clogic.pp_sequent  seq;
	   if must_finish seq then 
	     [seq]
	   else
	   try 
	     search (apply_rule_list_once rules seq ep)
	    with No_match -> 
               try
		 if may_finish seq then 
		   [seq]
		 else 
		   search ([Clogic.apply_or_left seq])
	       with No_match -> 
		 try 
		   search (Clogic.apply_or_right seq)
		 with No_match -> 
	           try 
	             let ts' = Smt.ask_the_audience seq.ts seq.obligation in 
	             search [[ {seq with ts = ts'} ]]
                   with 
                   | Assm_Contradiction -> []
                   | No_match ->
                   raise (Failed_eg [seq])
	 ) sequents 
      )
  in let res = apply_rule_list_inner sequents n in 
  if true || !(Debug.debug_ref) then Format.fprintf !dump "End time :%f @\n@?" (Sys.time ()); res


let check_imp logic seq = 
    try 
      ignore (apply_rule_list logic [seq] Smt.true_sequent_pimp Smt.true_sequent_pimp); true
    with  
      Failed -> false
    | Failed_eg x -> prover_counter_example := x ; false

let check_frm logic seq =
  try
    let leaves = apply_rule_list logic [seq] (fun _ -> false) Clogic.frame_sequent in 
    Some (Clogic.get_frames leaves)
  with 
    Failed -> Format.fprintf !(Debug.dump) "Foo55";None 
  | Failed_eg x -> Format.fprintf !(Debug.dump) "Foo44"; prover_counter_example := x; None 


let check_implication_frame_pform logic heap pheap  =  
  check_frm logic (Clogic.make_implies heap pheap)


let check_implication_pform logic heap pheap  =  
  check_imp logic (Clogic.make_implies heap pheap)


let abs logic ts_form  = 
  match check_frm logic  (Clogic.make_implies ts_form []) with 
    Some r -> r
  | None -> 
      (* Abstraction cannot fail *)
      assert false

let check_implication_syntactic logic pform pform2 = 
  let seq = Clogic.make_sequent (Clogic.convert_sequent ([],pform,pform2)) in
  match seq with 
    None -> true (* Found contradiction immediately *)
  | Some seq -> 
      check_imp logic seq

let check_implication_frame_syntactic logic pform pform2 = 
  let seq = Clogic.make_sequent (Clogic.convert_sequent ([],pform,pform2)) in
  match seq with 
    None -> Some [] (* Found contradiction immediately *)
  | Some seq -> 
      check_frm logic seq
    

let check_implication logic ts_form1 ts_form2 =
  let seq = Clogic.make_implies_inner ts_form1 ts_form2 in 
  check_imp logic seq 

let check_frame logic ts_form1 ts_form2 =
  let seq = Clogic.make_implies_inner ts_form1 ts_form2 in 
  check_frm logic seq 


let check_inconsistency logic ts_form   = assert false
(*  check_implication_inner logic ts heap1 ([],[],[False]) *)




let check_implies_list fl1 pf =
  List.for_all 
    (fun f1 -> 
      check_implication_pform empty_logic f1 pf
    ) fl1 


