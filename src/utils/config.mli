val specs_template_mode : bool ref
val dotty_print : bool ref
val symb_debug_ref : bool ref
val symb_debug : unit -> bool
val eclipse_ref : bool ref
val eclipse_mode : unit -> bool
val verb_proof_ref : bool ref
val verb_proof : unit -> bool
val parse_debug_ref : bool ref
val parse_debug : unit -> bool
val set_debug_char : char -> unit
val args_default : (string * Arg.spec * string) list
