type tactical =
	| Rules of Prover.sequent_rule list          (* try rules in order *)
	| Repeat of tactical                         (* repeat until fail *)
	| IfMatch of tactical * tactical * tactical  (* conditional *)

(* Running the prover with default_tactical rules *)
(* should be equivalent to running the oldimplementation *)
(* of the prover on rules *)
let default_tactical rules = Repeat (Rules rules)