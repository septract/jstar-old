(********************************************************
   This file is part of jStar
        src/jimplefront/classverification.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val is_interface : Jimple_global_types.jimple_file -> bool
val parent_classes_and_interfaces :
  Jimple_global_types.jimple_file -> Jparsetree.class_name list
val verify_exports_implications :
  (string * Psyntax.form * Psyntax.form) list -> Psyntax.logic -> unit
val verify_axioms_implications :
  Jparsetree.class_name ->
  Jimple_global_types.jimple_file ->
  (string * Psyntax.pform * Psyntax.form) list ->
  (Psyntax.form * Psyntax.form) Javaspecs.AxiomMap.t -> Psyntax.logic -> unit
val verify_methods :
  Jimple_global_types.jimple_file ->
  Javaspecs.methodSpecs ->
  Javaspecs.methodSpecs -> Psyntax.logic -> Psyntax.logic -> unit
