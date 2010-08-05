(********************************************************
   This file is part of jStar 
	src/prover/smt.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

open Clogic
open Congruence

let is_true_smt ts apred adisj opred odisj oeq oneq = 
     opred = RMSet.empty 
  && odisj = []
  && oeq = []
  && oneq = []


let true_sequent_pimp seq  =  
   seq.obligation.spat = RMSet.empty
   && 
   is_true_smt seq.ts seq.assumption.plain seq.assumption.disjuncts 
               seq.obligation.plain seq.obligation.disjuncts 
               seq.obligation.eqs seq.obligation.neqs 


