(********************************************************
   This file is part of jStar
        src/plugins/plugin_manager.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

val load_plugin : string -> unit
 
val run_abs_int : Psyntax.pform -> Psyntax.pform
