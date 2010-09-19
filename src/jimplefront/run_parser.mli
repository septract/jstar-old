val program_file_name : string ref
val logic_file_name : string ref
val spec_file_name : string ref
val absrules_file_name : string ref
val set_logic_file_name : string -> unit
val set_spec_file_name : string -> unit
val set_absrules_file_name : string -> unit
val set_program_file_name : string -> unit
val set_specs_template_mode : unit -> unit
val set_dotty_flag : unit -> unit
val set_grouped : unit -> unit
val set_eclipse : unit -> unit
val arg_list : (string * Arg.spec * string) list
val parse_program : unit -> Jimple_global_types.jimple_file
val main : unit -> unit
