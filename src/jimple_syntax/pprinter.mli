val binop2str : Jparsetree.binop -> string
val name2str : Jparsetree.name -> string
val class_name2str : Jparsetree.class_name -> string
val j_base_type2str : Jparsetree.j_base_type -> string
val list2str : ('a -> string) -> 'a list -> string -> string
val parameter2str : Jparsetree.nonvoid_type -> string
val j_type2str : Jparsetree.j_type -> string
val mkStrOfFieldSignature :
  Jparsetree.class_name -> Jparsetree.j_type -> Jparsetree.name -> string
val signature2str : Jparsetree.signature -> string
val variable2str : Jparsetree.variable -> string
val expression2str : Jparsetree.expression -> string
val statement2str : Jimple_global_types.statement_inner -> string

