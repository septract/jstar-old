(********************************************************
   This file is part of jStar
        src/plugins/plugin_callback.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Function to be called by a plugin for abstract interpretation *)
val add_abs_int : (Psyntax.pform -> Psyntax.pform) ref -> unit
