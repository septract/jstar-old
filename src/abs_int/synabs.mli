(********************************************************
   This file is part of jStar
        src/prover/abs.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

 (* Performs syntactic abstraction of F.ts_formula by eliminating existentials not appearing in spatial predicates *)
val kill_unused_existentials : Clogic.syntactic_form -> Clogic.syntactic_form
