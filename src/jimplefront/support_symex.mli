val file : string ref
val constant2args : Jparsetree.constant -> Psyntax.args
val default_for : Jparsetree.j_type -> Jparsetree.name -> Psyntax.args
val signature2args : Jparsetree.signature -> Psyntax.args
val name2args : Jparsetree.name -> Psyntax.args
val immediate2args : Jparsetree.immediate -> Psyntax.args
val variable2var : Jparsetree.variable -> Vars.var
val var2args : Vars.var -> Psyntax.args
val negate : Jparsetree.expression -> Jparsetree.expression
val this_var_name : string
val parameter : int -> string
val mk_this : Vars.var
val make_field_signature :
  Jparsetree.class_name ->
  Jparsetree.j_type -> Jparsetree.name -> Jparsetree.signature
