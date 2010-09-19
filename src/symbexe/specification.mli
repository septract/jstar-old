type ts_excep_post = Sepprover.inner_form Spec.ClassMap.t
val spec_conjunction : Spec.spec -> Spec.spec -> Spec.spec
exception Check_fails
val sub_spec : Psyntax.varmap -> Spec.spec -> Spec.spec
val jsr :
  Psyntax.logic ->
  Sepprover.inner_form ->
  Spec.spec -> (Sepprover.inner_form list * ts_excep_post list) option
val logical_vars_to_prog : Spec.spec -> Spec.spec
val refinement_extra :
  Psyntax.logic -> Spec.spec -> Spec.spec -> Psyntax.pform -> bool
val refinement : Psyntax.logic -> Spec.spec -> Spec.spec -> bool
