val binop2str : Jparsetree.binop -> string
val unop2str : Jparsetree.unop -> string
val nonstatic_invoke2str : Jparsetree.nonstatic_invoke -> string
val identifier2str : 'a -> 'a
val at_identifier2str : 'a -> 'a
val quoted_name2str : 'a -> 'a
val full_identifier2str : 'a -> 'a
val array_brackets2str : 'a -> 'a
val label_name2str : 'a -> 'a
val name2str : Jparsetree.name -> string
val class_name2str : Jparsetree.class_name -> string
val sign2str : Jparsetree.sign -> string
val constant2str : Jparsetree.constant -> string
val immediate2str : Jparsetree.immediate -> string
val fixed_array_descriptor2str : Jparsetree.immediate -> string
val array_descriptor2str : Jparsetree.immediate option -> string
val j_file_type2str : Jparsetree.j_file_type -> string
val modifier2str : Jparsetree.modifier -> string
val j_base_type2str : Jparsetree.j_base_type -> string
val list2str : ('a -> string) -> 'a list -> string -> string
val list_option2list : 'a list option -> 'a list
val nonvoid_type2str : Jparsetree.nonvoid_type -> string
val parameter2str : Jparsetree.nonvoid_type -> string
val j_type2str : Jparsetree.j_type -> string
val throws_clause2str : Jparsetree.class_name list option -> string
val case_label2str : Jparsetree.case_label -> string
val mkStrOfFieldSignature :
  Jparsetree.class_name -> Jparsetree.j_type -> Jparsetree.name -> string
val declaration2str : Jparsetree.declaration -> string
val case_statement2str : Jparsetree.case_statement -> string
val signature2str : Jparsetree.signature -> string
val reference2str : Jparsetree.reference -> string
val variable2str : Jparsetree.variable -> string
val invoke_expr2str : Jparsetree.invoke_expr -> string
val expression2str : Jparsetree.expression -> string
val bool_expr2str : Jparsetree.bool_expr -> string
val statement2str : Jimple_global_types.statement_inner -> string
val declaration_or_statement2str :
  Jimple_global_types.declaration_or_statement -> string
val catch_clause2str : Jparsetree.catch_clause -> string
val method_body2str :
  (Jimple_global_types.declaration_or_statement list *
   Jparsetree.catch_clause list)
  option -> string
val old_clauses2str :
  (Jimple_global_types.declaration_or_statement list *
   Jparsetree.catch_clause list)
  option list -> string
val member2str : Jimple_global_types.member -> string
val extends_clause2str : Jparsetree.class_name list -> string
val implements_clause2str : Jparsetree.class_name list -> string
val jimple_file2str : Jimple_global_types.jimple_file -> string
