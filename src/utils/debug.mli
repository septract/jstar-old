val safe : bool
val log_specs : int
val log_phase : int
val log_load : int
val log_prove : int
val log_exec : int
val log_logic : int
val log_active : int
val log : int -> bool
val logf : Format.formatter
val debug : bool
val buffer_dump : Buffer.t
val flagged_formatter : Format.formatter -> bool -> Format.formatter
val merge_formatters :
  Format.formatter -> Format.formatter -> Format.formatter
val proof_dump : Format.formatter ref
exception Unsupported
val unsupported : unit -> 'a
exception Unsupported2 of string
val unsupported_s : string -> 'a
val pp_list : ('a -> 'b -> unit) -> 'a -> 'b list -> unit
val string_of : (Format.formatter -> 'a -> 'b) -> 'a -> string
val form_format :
  string ->
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val form_format_optional :
  string ->
  string ->
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val list_format :
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val list_format_optional :
  string ->
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val toString : (Format.formatter -> 'a -> unit) -> 'a -> string
