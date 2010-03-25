(********************************************************
   This file is part of jStar 
	src/symbexe/specification.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(* Support functions for simbolic execution and misc conversion facilities *)


open Psyntax
open Sepprover
open Spec





type ts_excep_post = inner_form ClassMap.t 

let conjunction_excep excep_post f1 =
  ClassMap.map (fun post -> Psyntax.pconjunction post f1) excep_post

let conjunction_excep_convert excep_post f1 =
  ClassMap.map (fun post -> Sepprover.conjoin post f1) excep_post


let disjunction_excep excep_post1 excep_post2 =
  let newClassMap = ref ClassMap.empty in 
  let _ = ClassMap.iter 
      (fun key post -> 
	newClassMap := 
	  ClassMap.add 
	    key 
	    (try Psyntax.mkOr(post,(ClassMap.find key excep_post2))
	    with Not_found -> post)
	    !newClassMap 
      ) 
    excep_post1 in
  let _ = ClassMap.iter
      (fun key post -> 
	if ClassMap.mem key excep_post1 then () 
	else newClassMap := ClassMap.add key post !newClassMap)
      excep_post2
  in !newClassMap



(*
type spec = 
    { pre : representative Plogic.pform;
      post : representative Plogic.pform;
      excep : excep_post }
*)

let spec_conjunction spec1 spec2 =
  let var = Arg_var(Vars.freshe()) in
  let zero = Arg_string("**first**") in
  let one = Arg_string("**second**") in
  let eq = mkEQ(var,zero) in 
  let neq = mkEQ(var,one) in       
  match spec1,spec2 with 
    {pre=pre1; post=post1; excep=excep1},
    {pre=pre2; post=post2; excep=excep2} ->
      {pre= Psyntax.mkOr ((Psyntax.pconjunction pre1 eq),(Psyntax.pconjunction pre2 neq));
       post= Psyntax.mkOr ((Psyntax.pconjunction post1 eq),(Psyntax.pconjunction post2 neq));
       excep = disjunction_excep (conjunction_excep excep1 eq) (conjunction_excep excep2 neq)
     }



(***************************************
   Refinement type stuff 
 ***************************************)


(* 
   { e1 : f1} , ... , {en :  fn}   (excep1)  
   ===>
   { e1' : f1', ... , {em' : fm'}  (excep2)
iff
forall ei :fi. exists ej' : fj'.  ei=ej' /\ fi==>fj'
*)
exception Check_fails

let implication_excep logic excep1 excep2 = 
  try 
    ClassMap.iter (
    fun exname form -> 
      if Sepprover.implies logic form (ClassMap.find exname excep2) 
      then ()
      else raise Check_fails
   ) excep1; true
  with check_fails -> false

let sub_spec  sub spec =
  match spec with 
    {pre=pre; post=post; excep=excep} ->
      {pre=subst_pform sub pre;
       post=subst_pform sub post;
	excep=ClassMap.map (subst_pform sub) excep;}
      
let ev_spec spec = 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let ev = ev_form spec_pre in 
      let ev = ev_form_acc spec_post ev in 
      let ev = ClassMap.fold (fun key ex vs -> ev_form_acc ex vs) spec_excep ev in 
      ev

let ev_spec_pre spec = 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let ev = ev_form spec_pre in 
      ev

let jsr logic (pre : inner_form) (spec : spec)  : (inner_form  list * ts_excep_post list) option  = 
  let ev = ev_spec spec in 
  let subst = subst_kill_vars_to_fresh_exist ev in 
  let spec = sub_spec subst spec in 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let frame_list = Sepprover.frame logic pre spec_pre in 
      match frame_list with
	None -> None
      |	Some frame_list -> 
	let res = Misc.map_option (fun post -> (*Prover.tidy_one*) try Some (Sepprover.conjoin spec_post post) with Contradiction -> None) frame_list in 
	let excep_res = List.map (conjunction_excep_convert spec_excep) frame_list in 
	let res = List.map (fun ts -> vs_fold (fun e ts -> kill_var e ts) ev ts) res in 
	Some (res,excep_res)

let logical_vars_to_prog spec2 = 
  let ev = ev_spec_pre spec2 in 
  let sub = subst_kill_vars_to_fresh_prog ev in 
  sub_spec sub spec2 

(*  spec2={P}{Q} =[extra]=> spec1  
 
   {P*extra}{Q} ===> spec1
*)
let refinement_extra (logic : logic) (spec1 : spec) (spec2 : spec) (extra : pform): bool =
  let spec2 = logical_vars_to_prog spec2 in 
  match spec2 with
    {pre=pre; post=post; excep=excep} ->
      match (Sepprover.convert (extra&&&pre)) with 
	None -> true
      |	Some form -> 
	  match jsr logic form spec1 with 
	    None -> false
	  | Some (newposts, newexcep_posts) ->
	      let res = List.for_all (fun newpost -> Sepprover.implies logic newpost post) newposts in 
	      let res2 = List.for_all (fun newexcep_post -> implication_excep logic newexcep_post excep) newexcep_posts in 
	      (res&&res2)


(*  spec2 ==> spec1 
That is
   spec2
   -----
     :
   ----- 
   spec1  
*)
let refinement (logic : logic) (spec1 : spec) (spec2 : spec) : bool =
    refinement_extra logic spec1 spec2 [] 



