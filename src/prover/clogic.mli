exception Failed
exception Assm_Contradiction
module RMSet :
  sig
    type t = string * Cterm.term_handle
    type multiset
    val is_empty : multiset -> bool
    val has_more : multiset -> bool
    val next : multiset -> multiset
    val remove : multiset -> t * multiset
    val restart : multiset -> multiset
    val iter : (t -> unit) -> multiset -> unit
    val fold : ('a -> t -> 'a) -> 'a -> multiset -> 'a
    val lift_list : t list -> multiset
    val union : multiset -> multiset -> multiset
    val empty : multiset
    val intersect : multiset -> multiset -> multiset * multiset * multiset
    val back : multiset -> int -> multiset
    val map_to_list :
      multiset -> (string * Cterm.term_handle -> 'a) -> 'a list
  end
type multiset = RMSet.multiset
module SMSet :
  sig
    type t = string * Psyntax.args list
    type multiset
    val is_empty : multiset -> bool
    val has_more : multiset -> bool
    val next : multiset -> multiset
    val remove : multiset -> t * multiset
    val restart : multiset -> multiset
    val iter : (t -> unit) -> multiset -> unit
    val fold : ('a -> t -> 'a) -> 'a -> multiset -> 'a
    val lift_list : t list -> multiset
    val union : multiset -> multiset -> multiset
    val empty : multiset
    val intersect : multiset -> multiset -> multiset * multiset * multiset
    val back : multiset -> int -> multiset
    val map_to_list :
      multiset -> (string * Psyntax.args list -> 'a) -> 'a list
  end
type syntactic_form = {
  sspat : SMSet.multiset;
  splain : SMSet.multiset;
  sdisjuncts : (syntactic_form * syntactic_form) list;
  seqs : (Psyntax.args * Psyntax.args) list;
  sneqs : (Psyntax.args * Psyntax.args) list;
}
type formula = {
  spat : RMSet.multiset;
  plain : RMSet.multiset;
  disjuncts : (formula * formula) list;
  eqs : (Cterm.term_handle * Cterm.term_handle) list;
  neqs : (Cterm.term_handle * Cterm.term_handle) list;
}
type ts_formula = {
  ts : Cterm.term_structure;
  form : formula;
  cache_sform : syntactic_form option ref;
}
val mk_ts_form : Cterm.term_structure -> formula -> ts_formula
val kill_var : ts_formula -> Vars.var -> ts_formula
val update_var_to : ts_formula -> Vars.var -> Psyntax.args -> ts_formula
val pp_ts_formula : Format.formatter -> ts_formula -> unit
val empty : formula
val truth : formula
val normalise :
  Cterm.term_structure -> formula -> formula * Cterm.term_structure
val convert_to_inner : Psyntax.pform -> syntactic_form
val conjoin : bool -> ts_formula -> syntactic_form -> ts_formula
type sequent = {
  matched : RMSet.multiset;
  ts : Cterm.term_structure;
  assumption : formula;
  obligation : formula;
}
val plain : formula -> bool 
val pp_sequent : Format.formatter -> sequent -> unit
val true_sequent : sequent -> bool
val frame_sequent : sequent -> bool
type sequent_rule =
    Psyntax.psequent * Psyntax.psequent list list * string *
    (Psyntax.pform * Psyntax.pform) * Psyntax.where list
type pat_sequent = {
  assumption_same : syntactic_form;
  assumption_diff : syntactic_form;
  obligation_diff : syntactic_form;
}
val convert_sequent : Psyntax.psequent -> pat_sequent
type inner_sequent_rule = {
  conclusion : pat_sequent;
  premises : pat_sequent list list;
  name : string;
  without_left : syntactic_form;
  without_right : syntactic_form;
  where : Psyntax.where list;
}
val convert_rule : sequent_rule -> inner_sequent_rule
val make_sequent : pat_sequent -> sequent option
val check : Psyntax.where list -> sequent -> bool
val simplify_sequent : Psyntax.rewrite_rule list -> sequent -> sequent option
val apply_rule : inner_sequent_rule -> sequent -> sequent list list
val apply_or_left : sequent -> sequent list
val apply_or_right : sequent -> sequent list list
val get_frame : sequent -> ts_formula
val get_frames : sequent list -> ts_formula list
val convert_with_eqs : bool -> Psyntax.pform -> ts_formula
val convert :
  bool ->
  Cterm.term_structure -> Psyntax.pform -> formula * Cterm.term_structure
val make_implies : ts_formula -> Psyntax.pform -> sequent
val make_syntactic : ts_formula -> syntactic_form
val make_implies_inner : ts_formula -> ts_formula -> sequent
val abs : ts_formula -> ts_formula 
