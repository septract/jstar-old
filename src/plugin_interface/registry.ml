(********************************************************
   This file is part of jStar
        src/plugins/registry.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Registry of plugins for abstract interpretation *)
let abs_int_registry : ((Psyntax.pform -> Psyntax.pform) ref) list ref = ref []
