(********************************************************
   This file is part of jStar
        src/symbexe/specification.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


type ts_excep_post = Sepprover.inner_form Spec.ClassMap.t
type symb_form =
  {
    heap : Sepprover.inner_form;
    antiheap : Sepprover.inner_form;
  }
val empty_inner_form : Sepprover.inner_form
val spec_conjunction : Spec.spec -> Spec.spec -> Spec.spec
val sub_spec : Psyntax.varmap -> Spec.spec -> Spec.spec
val jsr :
  Psyntax.logic ->
  Sepprover.inner_form ->
  Sepprover.inner_form option ->
  Spec.spec -> (symb_form list) option
val logical_vars_to_prog : Spec.spec -> Spec.spec
val refinement_extra :
  Psyntax.logic -> Spec.spec -> Spec.spec -> Psyntax.pform -> bool
val refinement : Psyntax.logic -> Spec.spec -> Spec.spec -> bool
