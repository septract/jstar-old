(********************************************************
   This file is part of jStar
        src/parsing/support_syntax.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val bop_to_prover_arg : Jparsetree.binop -> string
val bop_to_prover_pred :
  Jparsetree.binop -> Psyntax.args -> Psyntax.args -> Psyntax.pform_at list
val parameter : int -> string
val parameter_var : int -> Vars.var
val this_var_name : string
val this_var : Vars.var
val res_var_name : string
val res_var : Vars.var
