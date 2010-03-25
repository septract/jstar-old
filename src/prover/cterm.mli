(********************************************************
   This file is part of jStar 
	src/prover/cterm.mli
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
open Congruence
open Psyntax

type term_structure

type representative

type pattern 

(*
   Create a new term structure
   It is externally functional, however underneath it uses mutation, 
   so best to create new ones, rather than having a single starting one.
*)
val new_ts : unit -> term_structure

(* Convert a Psyntax.args with AnyVars into a pattern to match *)
(*val make_pattern : Psyntax.args -> term_structure -> (pattern * term_structure)))))))))*)

val unifies : term_structure -> pattern -> representative -> (term_structure -> 'a) -> 'a

val determined_exists : term_structure -> representative -> representative -> term_structure  * (representative * representative) list


(* Match pattern against the representative in the current term structure, 
   the new term structure (with the unified variables) will be passed to the continuation 
   Will raise No_match if no match can be found.
   Continutation can cause back tracking of pattern match by raising No_match
*)
(*val match_pattern : term_structure -> pattern -> representative -> (term_structure -> 'a) -> 'a*)

(*
   Add Psyntax to the term_structure, and return a representative and updated term structure
*)
val add_term : bool -> Psyntax.args -> term_structure -> (representative * term_structure)

val add_pattern : Psyntax.args -> term_structure -> (pattern * term_structure)

val equal : term_structure -> representative -> representative -> bool

val unify_patterns : term_structure -> pattern -> pattern -> (term_structure -> 'a) -> 'a

val not_equal : term_structure -> representative -> representative -> bool

val unify_not_equal_pattern : term_structure -> pattern -> pattern -> (term_structure -> 'a) -> 'a

val make_equal : term_structure -> representative -> representative -> term_structure

val normalise : term_structure -> representative -> representative 

(*
   Return a compressed term_structure, will remove redundant terms.
*)
val compress : term_structure -> term_structure * (representative -> representative)

val make_not_equal : term_structure -> representative -> representative -> term_structure

val add_tuple : bool -> Psyntax.args list -> term_structure -> representative * term_structure 

val make_tuple_pattern : Psyntax.args list -> term_structure -> pattern * term_structure 


val make_equal_t : bool -> term_structure -> Psyntax.args -> Psyntax.args -> term_structure
val make_not_equal_t : bool -> term_structure -> Psyntax.args -> Psyntax.args -> term_structure


val blank_pattern_vars : term_structure -> term_structure

val pp_ts : Format.formatter -> term_structure -> unit 

val pp_c : term_structure -> Format.formatter -> representative -> unit
val has_pp_c : term_structure -> representative -> bool

val get_eqs : term_structure -> (Psyntax.args * Psyntax.args) list
val get_neqs : term_structure -> (Psyntax.args * Psyntax.args) list

val get_term : term_structure -> representative-> Psyntax.args
val kill_var : term_structure -> Vars.var -> term_structure 
val update_var_to : term_structure -> Vars.var -> Psyntax.args -> term_structure

val rewrite : term_structure -> rewrite_rule list -> (term_structure * rewrite_guard -> bool) -> term_structure

val ts_eq : term_structure -> term_structure -> bool

val var_not_used_in : term_structure -> Vars.var -> representative list -> bool
