(********************************************************
   This file is part of jStar 
	src/symbexe/symbexespec.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

open Psyntax
open Spec

type logic = Psyntax.logic
type formula = Psyntax.pform
type pformula = Sepprover.inner_form (* stands for 'prover' formula *)
type ex = Spec.excep_post
type pex = pformula Spec.ClassMap.t  (* stands for 'prover' exceptional ... *)
type spec = Spec.spec


let conjunction_excep_convert excep_post f1 =
  ClassMap.map (fun post -> Sepprover.conjoin post f1) excep_post

exception Check_fails (* TODO(rgrig): get rid of this? *)
let implication_excep logic excep1 excep2 = 
  try 
    ClassMap.iter (
    fun exname form -> 
      if Sepprover.implies logic form (ClassMap.find exname excep2) 
      then ()
      else raise Check_fails
   ) excep1; true
  with check_fails -> false

let jsr logic pre spec = 
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
	let res = List.map (fun ts -> vs_fold (fun e ts -> Sepprover.kill_var e ts) ev ts) res in 
	Some (res,excep_res)

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

let refinement (logic : logic) (spec1 : spec) (spec2 : spec) : bool =
    refinement_extra logic spec1 spec2 [] 
