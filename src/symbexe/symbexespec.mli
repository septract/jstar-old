(********************************************************
   This file is part of jStar 
	src/symbexe/symbexespec.mli
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

(** 
  These are utilities to process specifications (formulas) using the
  prover. They are used by symbexe. Other utilities, which do *not* use
  the prover are in src/symbexe_syntax.
 *)

type logic = Psyntax.logic
type formula = Psyntax.formula
type pformula = Sepprover.inner_form (* stands for 'prover' formula *)
type ex = Spec.excep_post
type spec = Spec.spec

val conjunction_excep_convert : ex -> formula -> ex
(** Conjoin a formula to all postconditions. *) 

val implication_excep : logic -> e1 : ex -> e2 : ex -> bool
(** Does [e1] imply [e2] for all classes (in [e1])? *)

val jsr : logic -> pformula -> spec -> (pformula list * ex list) option

val refinement_extra : logic -> spec1 : spec -> spec2 : spec -> extra : formula -> bool
(*  spec2={P}{Q} =[extra]=> spec1  
   {P*extra}{Q} ===> spec1  *)

val refinement : logic -> spec1 : spec -> spec2 : spec -> bool
(*  spec2 ==> spec1 
That is
   spec2
   -----
     :
   ----- 
   spec1  
*)

