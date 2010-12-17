(********************************************************
   This file is part of jStar
        src/plugins/plugin_manager.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* Loads plugin using (nat) dynlink *)
let load_plugin (filename : string) =
   try Dynlink.loadfile (Dynlink.adapt_filename filename)
   with Dynlink.Error e -> failwith (Dynlink.error_message e)

(* Runs abstract interpretation plugins on a given pform *)
let run_abs_int (pheap : Psyntax.pform) =
  List.fold_left (fun pform abs_int -> abs_int pform) pheap !Registry.abs_int_registry
