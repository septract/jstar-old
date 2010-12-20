(********************************************************
   This file is part of jStar
        src/plugins/plugin_callback.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Function to be called by a plugin for abstract interpretation *)
let add_abs_int (impl : Psyntax.pform -> Psyntax.pform) =
  Registry.abs_int_registry := !Registry.abs_int_registry @ [impl]
