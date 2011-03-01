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

 
(* Loads plugin using (nat) dynlink *)
val load_plugin : string -> unit


(* Runs abstract_val from abstract interpretation plugins on a given pform *)
val abstract_val : Psyntax.pform -> Psyntax.pform

(* Runs join from abstract interpretation plugins on given pforms *)
val join : Psyntax.pform -> Psyntax.pform -> Psyntax.pform list

(* Runs meet from abstract interpretation plugins on given pforms *)
val meet : Psyntax.pform -> Psyntax.pform -> Psyntax.pform list

(* Runs widening from abstract interpretation plugins on given pforms *)
val widening : Psyntax.pform -> Psyntax.pform -> Psyntax.pform list
