(********************************************************
   This file is part of jStar 
	src/symbexe_syntax/spec.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
open Psyntax
(*open Sepprover*)


module ClassMap =   
  Map.Make(struct
    type t = string
    let compare = compare
  end)

module LabelMap =
  Map.Make(struct
    type t = string
    let compare = compare
  end)

type excep_post = Psyntax.pform ClassMap.t 
type inv_map = Psyntax.pform LabelMap.t

type spec = 
    { pre : Psyntax.pform;
      post : Psyntax.pform;
      excep : excep_post;
      inv : inv_map }

let mk_spec pre post excep inv = 
    { pre=pre;
      post=post;
      excep=excep;
      inv=inv
    }

let spec2str ppf (spec: spec)  = 
  Format.fprintf ppf "@[{%a}@]@ @[{%a}@]"
    Psyntax.string_form spec.pre
    Psyntax.string_form spec.post

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  


(*** support functions for symbolic execution and misc conversion facilities *)

let conjunction_excep excep_post f1 =
  ClassMap.map (fun post -> Psyntax.pconjunction post f1) excep_post

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


let spec_conjunction spec1 spec2 =
  let var = Arg_var(Vars.freshe()) in
  let zero = Arg_string("**first**") in
  let one = Arg_string("**second**") in
  let eq = mkEQ(var,zero) in 
  let neq = mkEQ(var,one) in       
  match spec1,spec2 with 
    {pre=pre1; post=post1; excep=excep1; inv=inv1},
    {pre=pre2; post=post2; excep=excep2; inv=inv2} ->
      {pre= Psyntax.mkOr ((Psyntax.pconjunction pre1 eq),(Psyntax.pconjunction pre2 neq));
       post= Psyntax.mkOr ((Psyntax.pconjunction post1 eq),(Psyntax.pconjunction post2 neq));
       excep = disjunction_excep (conjunction_excep excep1 eq) (conjunction_excep excep2 neq);
       inv = inv1 @ inv2
     }



(*** refinement type stuff *)


let sub_spec  sub spec =
  match spec with 
    {pre=pre; post=post; excep=excep; inv=inv} ->
      {pre=subst_pform sub pre;
       post=subst_pform sub post;
       excep=ClassMap.map (subst_pform sub) excep;
       inv=List.map (fun (l, i) -> (l, subst_pform sub i)) inv}
      
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

let logical_vars_to_prog spec2 = 
  let ev = ev_spec_pre spec2 in 
  let sub = subst_kill_vars_to_fresh_prog ev in 
  sub_spec sub spec2 


(* TODO Should add stuff for internal representation of symbolic execution *)
