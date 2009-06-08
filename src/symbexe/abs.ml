(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(* ddino: implementation of abstraction rules *)

open Rlogic 
open Vars

(* this corresponds to St1/St2 abstratin rules in TACAS 06 paper*)
let remove_existentials (sheap: Rlogic.ts_form) =
  sheap
(*
  let rec scan_pure eql tobeadded sh =
    match eql with
    | [] -> tobeadded,sh
    | (EQ(a1,a2) as eq)::eql'->
	(match a1,a2 with 
	 | Arg_var(EVar (v',v'')) , _ -> 
	     let subs=add (EVar (v',v'')) a2 empty in
	     let sh'=subst_form subs (eql', snd sh) in
	     scan_pure (fst sh') tobeadded sh' 
	 | _ ,Arg_var(EVar (v',v'')) ->
	     let subs=add (EVar(v',v'')) a1 empty in
	     let sh'=subst_form subs (eql', snd sh) in
	     scan_pure (fst sh') tobeadded sh' 
	 | _,_ -> scan_pure eql' (eq::tobeadded) (eql', snd sh) 
	)
    | p::eql' -> scan_pure eql' (p::tobeadded) (eql', snd sh) 
  in 
  let tba, h = scan_pure (fst sheap) [] sheap in
  (tba @ (fst h), snd h)
*)

(* apply the abstraction function *)
let apply_abstraction (abs_rules : Prover.logic) (sheap : Rlogic.ts_form) =
  (*let heap=remove_existentials sheap in *)
  let heap = sheap in 
  Prover.tidy (Prover.abs abs_rules heap )

