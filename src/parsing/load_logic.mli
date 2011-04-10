(********************************************************
   This file is part of jStar
        src/parsing/load_logic.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* TODO(rgrig): replace tuple by record *)

val load_logic_extra_rules :
  string list ->
  string ->
  Psyntax.rules Load.importoption list ->
  Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list

val load_logic :
  string ->
  Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list
  (** [load_logic f] loads logic file [f] (see [Cli_utils]) and parses it. *)

val load_abstractions :
  string ->
  Psyntax.sequent_rule list * Psyntax.rewrite_rule list * string list
  (** [load_abstractions f] loads logic file [f] (see [Cli_utils]) and 
  parses it. *)

