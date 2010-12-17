(********************************************************
   This file is part of jStar
        src/prover/prover.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val pprint_counter_example : Format.formatter -> unit -> unit
val print_counter_example : unit -> unit
val get_counter_example : unit -> string
val pprint_proof : Format.formatter -> unit
val string_of_proof : unit -> string
val check_implication_frame_pform :
  Psyntax.logic ->
  Clogic.F.ts_formula -> Psyntax.pform -> Clogic.F.ts_formula list option
val check_implication_pform :
  Psyntax.logic -> Clogic.F.ts_formula -> Psyntax.pform -> bool
val abs : Psyntax.logic -> Clogic.F.ts_formula -> Clogic.F.ts_formula list
val check_implication :
  Psyntax.logic -> Clogic.F.ts_formula -> Clogic.F.ts_formula -> bool
val check_frame :
  Psyntax.logic ->
  Clogic.F.ts_formula -> Clogic.F.ts_formula -> Clogic.F.ts_formula list option
val check_inconsistency : Psyntax.logic -> Clogic.F.ts_formula -> bool
val check_implies_list : Clogic.F.ts_formula list -> Psyntax.pform -> bool
val check_abduction_pform :
  Psyntax.logic -> Clogic.F.ts_formula -> Psyntax.pform -> Clogic.AF.ts_formula list option
(*val kill_unused_existentials : Clogic.F.ts_formula -> Clogic.F.ts_formula*)
