val core_debug : unit -> bool
val args2str : Psyntax.args -> string
val args_list2str : Psyntax.args list -> string
val args_fldlist2str : (string * Psyntax.args) list -> string
val form_at2str : Psyntax.pform_at -> string
val list_form2str : Psyntax.pform -> string
val variable_list2str : Format.formatter -> Vars.var list -> unit
val pp_stmt_core : Format.formatter -> Core.core_statement -> unit
