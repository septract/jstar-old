type core_statement =
    Nop_stmt_core
  | Label_stmt_core of string
  | Assignment_core of Vars.var list * Spec.spec * Psyntax.args list
  | Goto_stmt_core of string list
  | Throw_stmt_core of Psyntax.args
  | End
type symb_question =
    Specification of string * Spec.spec * core_statement list
type symb_test = Nothing_here_yet
