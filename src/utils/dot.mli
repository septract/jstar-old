(********************************************************
   This file is part of jStar 
	src/utils/dot.mli
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

(** Handling of graphviz (.dot) files. *)

val escape_for_label : string -> string
(** [escape_for_label s] is what should be put in a .dot file so that
  the user sees [s] when viewing the .dot file. *)
