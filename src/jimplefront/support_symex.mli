val file : string ref
val variable2key : Jparsetree.variable -> string
val constant2args : Jparsetree.constant -> Psyntax.args
val default_for : Jparsetree.j_type -> Jparsetree.name -> Psyntax.args
val signature2args : Jparsetree.signature -> Psyntax.args
val name2args : Jparsetree.name -> Psyntax.args
val identifier2args : Vars.StrVarHash.key -> Psyntax.args
val immediate2args : Jparsetree.immediate -> Psyntax.args
val reference2args : Jparsetree.reference -> 'a
val expression2args : Jparsetree.expression -> Psyntax.args
val variable2var : Jparsetree.variable -> Vars.var
val var2args : Vars.var -> Psyntax.args
val immediate2var : Jparsetree.immediate -> Vars.var
val form2str : Format.formatter -> Psyntax.form -> unit
val print_formset : string -> Sepprover.inner_form list -> unit
val negate : Jparsetree.expression -> Jparsetree.expression
val expression2pure : Jparsetree.expression -> Psyntax.pform_at list
val get_class_name_from_signature :
  Jparsetree.signature -> Jparsetree.class_name
val signature_get_name : Jparsetree.signature -> Jparsetree.name
val invoke_exp_get_signature : Jparsetree.invoke_expr -> Jparsetree.signature
val this_var_name : string
val parameter : int -> string
val mk_this : Vars.var
val mk_res : Vars.var
val make_field_signature :
  Jparsetree.class_name ->
  Jparsetree.j_type -> Jparsetree.name -> Jparsetree.signature
