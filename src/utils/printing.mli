(********************************************************
   This file is part of jStar
        src/utils/printing.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


type source_location = {
  begin_line : int;
  begin_column : int;
  end_line : int;
  end_column : int;
}
val add_location : int -> source_location option -> unit
val pp_json_location_opt : source_location option -> string -> string -> unit
val pp_json_node : int -> string -> string -> unit
type sep_wrapper = {
  separator :
    'a.
      (Format.formatter -> 'a -> unit) ->
      Format.formatter -> bool -> 'a -> bool;
}
val pp_sep : string -> sep_wrapper
val pp_star : sep_wrapper
val pp_whole : ('a -> 'b -> bool -> 'c -> 'd) -> 'a -> 'b -> 'c -> unit
val pp_eq :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a * 'a -> unit
val pp_neq :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a * 'a -> unit
val pp_disjunct :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a * 'a -> unit
