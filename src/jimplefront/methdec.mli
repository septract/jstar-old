val make_methdec :
  Jparsetree.modifier list ->
  Jparsetree.class_name ->
  Jparsetree.j_type ->
  Jparsetree.name ->
  Jparsetree.parameter list ->
  Jparsetree.throws_clause ->
  Jparsetree.local_var list * Jimple_global_types.statement list ->
  Jimple_global_types.statement list list ->
  Jparsetree.local_var list * Jimple_global_types.statement list ->
  Jparsetree.local_var list * Jimple_global_types.statement list ->
  Jimple_global_types.methdec_jimple
val get_list_methods :
  Jimple_global_types.jimple_file -> Jimple_global_types.member list
val get_list_member :
  Jimple_global_types.jimple_file -> Jimple_global_types.member list
val get_list_fields :
  Jimple_global_types.jimple_file -> Jimple_global_types.member list
val get_class_name : Jimple_global_types.jimple_file -> Jparsetree.class_name
val get_locals :
  (Jimple_global_types.declaration_or_statement list * 'a) option ->
  (Jparsetree.j_type option * Jparsetree.name) list
val make_stmts_list :
  (Jimple_global_types.declaration_or_statement list * 'a) option ->
  Jimple_global_types.statement list
val member2methdec :
  Jparsetree.class_name ->
  Jimple_global_types.member -> Jimple_global_types.methdec_jimple option
val make_methdecs_of_list :
  Jparsetree.class_name ->
  Jimple_global_types.member list -> Jimple_global_types.methdec_jimple list
val get_msig :
  Jimple_global_types.methdec_jimple ->
  'a -> 'a * Jparsetree.j_type * Jparsetree.name * Jparsetree.parameter list
val has_body : Jimple_global_types.methdec_jimple -> bool
val has_requires_clause : Jimple_global_types.methdec_jimple -> bool
val has_ensures_clause : Jimple_global_types.methdec_jimple -> bool
