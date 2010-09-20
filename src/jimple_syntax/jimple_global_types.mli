type statement_inner =
    Label_stmt of Jparsetree.label_name
  | Breakpoint_stmt
  | Entermonitor_stmt of Jparsetree.immediate
  | Exitmonitor_stmt of Jparsetree.immediate
  | Tableswitch_stmt of Jparsetree.immediate * Jparsetree.case_statement list
  | Lookupswitch_stmt of Jparsetree.immediate *
      Jparsetree.case_statement list
  | Identity_stmt of Jparsetree.name * Jparsetree.at_identifier *
      Jparsetree.j_type
  | Identity_no_type_stmt of Jparsetree.name * Jparsetree.at_identifier
  | Assign_stmt of Jparsetree.variable * Jparsetree.expression
  | If_stmt of Jparsetree.expression * Jparsetree.label_name
  | Goto_stmt of Jparsetree.label_name
  | Nop_stmt
  | Ret_stmt of Jparsetree.immediate option
  | Return_stmt of Jparsetree.immediate option
  | Throw_stmt of Jparsetree.immediate
  | Invoke_stmt of Jparsetree.invoke_expr
  | Spec_stmt of Vars.var list * Spec.spec
type statement = statement_inner * Printing.source_location option
type declaration_or_statement =
    DOS_dec of Jparsetree.declaration
  | DOS_stm of statement
type method_body =
    (declaration_or_statement list * Jparsetree.catch_clause list) option
type requires_clause = method_body
type old_clauses = method_body list
type ensures_clause = method_body
type member =
    Field of Jparsetree.modifier list * Jparsetree.j_type * Jparsetree.name
  | Method of Jparsetree.modifier list * Jparsetree.j_type *
      Jparsetree.name * Jparsetree.parameter list *
      Jparsetree.throws_clause * requires_clause * old_clauses *
      ensures_clause * method_body
type jimple_file =
    JFile of Jparsetree.modifier list * Jparsetree.j_file_type *
      Jparsetree.class_name * Jparsetree.extends_clause *
      Jparsetree.implements_clause * member list
type methdec_jimple = {
  modifiers : Jparsetree.modifier list;
  class_name : Jparsetree.class_name;
  ret_type : Jparsetree.j_type;
  name_m : Jparsetree.name;
  params : Jparsetree.parameter list;
  locals : Jparsetree.local_var list;
  th_clause : Jparsetree.throws_clause;
  req_locals : Jparsetree.local_var list;
  mutable req_stmts : statement list;
  mutable old_stmts_list : statement list list;
  ens_locals : Jparsetree.local_var list;
  mutable ens_stmts : statement list;
  mutable bstmts : statement list;
}
