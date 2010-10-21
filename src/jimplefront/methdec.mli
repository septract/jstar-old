(********************************************************
   This file is part of jStar
        src/jimplefront/methdec.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val get_list_methods :
  Jimple_global_types.jimple_file -> Jimple_global_types.member list
val get_list_fields :
  Jimple_global_types.jimple_file -> Jimple_global_types.member list
val get_class_name : Jimple_global_types.jimple_file -> Jparsetree.class_name
val make_methdecs_of_list :
  Jparsetree.class_name ->
  Jimple_global_types.member list -> Jimple_global_types.methdec_jimple list
val get_msig :
  Jimple_global_types.methdec_jimple ->
  'a -> 'a * Jparsetree.j_type * Jparsetree.name * Jparsetree.parameter list
val has_body : Jimple_global_types.methdec_jimple -> bool
val has_requires_clause : Jimple_global_types.methdec_jimple -> bool
val has_ensures_clause : Jimple_global_types.methdec_jimple -> bool
