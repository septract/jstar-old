val getenv_dirlist : string -> string list
val string_of_file : string -> string
val parse_file : ('a -> Lexing.lexbuf -> 'b) -> 'a -> string -> string -> 'b
val find_file_from_dirs : string list -> string -> string
val terminal_red : string
val terminal_green : string
val terminal_white : string
