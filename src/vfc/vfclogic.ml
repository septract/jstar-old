(* Verified Featherweight C logic support *)

open Psyntax


(* create x.f |-> e *)
let mk_pointsto x f e = mkPPred("field", [x; f; e])
