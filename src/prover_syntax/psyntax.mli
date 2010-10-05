exception Contradiction
type args =
    Arg_var of Vars.var
  | Arg_string of string
  | Arg_op of string * args list
  | Arg_cons of string * args list
  | Arg_record of (string * args) list
val mkArgRecord : (string * args) list -> args
type fldlist = (string * args) list
module VarSet :
  sig
    type elt = Vars.var
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
  end
type varset = VarSet.t
val vs_add : VarSet.elt -> VarSet.t -> VarSet.t
val vs_empty : VarSet.t
val vs_is_empty : VarSet.t -> bool
val vs_union : VarSet.t -> VarSet.t -> VarSet.t
val vs_inter : VarSet.t -> VarSet.t -> VarSet.t
val vs_diff : VarSet.t -> VarSet.t -> VarSet.t
val vs_fold : (VarSet.elt -> 'a -> 'a) -> VarSet.t -> 'a -> 'a
val vs_for_all : (VarSet.elt -> bool) -> VarSet.t -> bool
val vs_from_list : VarSet.elt list -> VarSet.t
module VarMap :
  sig
    type key = Vars.var
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end
type 'a varmap_t = 'a VarMap.t
type varmapargs = args varmap_t
module VarHash :
  sig
    type key = Vars.var
    type 'a t
    val create : int -> 'a t
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
  end
type varhashargs = args VarHash.t
type 'a varhash_t = 'a VarHash.t
type varmap = Plain of varmapargs | Freshen of varmapargs * varhashargs
val find : VarMap.key -> varmap -> args
val add : VarMap.key -> args -> varmap -> varmap
val empty : varmap
val subst_args : varmap -> args -> args
val string_args : Format.formatter -> args -> unit
val string_args_list : Format.formatter -> args list -> unit
val ev_args : args -> VarSet.t -> VarSet.t
val ev_args_list : args list -> VarSet.t -> VarSet.t
val fv_args : args -> VarSet.t -> VarSet.t
val fv_args_list : args list -> VarSet.t -> VarSet.t
type pform_at =
    P_EQ of args * args
  | P_NEQ of args * args
  | P_PPred of string * args list
  | P_SPred of string * args list
  | P_Wand of pform * pform
  | P_Or of pform * pform
  | P_Septract of pform * pform
  | P_Garbage
  | P_False
and pform = pform_at list
val pconjunction : pform -> pform -> pform
val ( &&& ) : pform -> pform -> pform
val mkGarbage : pform_at list
val subst_pform : varmap -> pform -> pform
type psequent = pform * pform * pform
val purify : pform_at list -> pform_at list
type varterm = Var of varset
type where = 
  | NotInContext of varterm 
  | NotInTerm of varterm * args
  | PureGuard of pform 
type sequent_rule =
    psequent * psequent list list * string * (pform * pform) * where list
val pp_sequent_rule : Format.formatter -> sequent_rule -> unit
type rewrite_guard = {
  without_form : pform;
  if_form : pform;
  rewrite_where : where list;
}
type rewrite_rule = {
  function_name : string;
  arguments : args list;
  result : args;
  guard : rewrite_guard;
  rewrite_name : string;
  saturate : bool;
}
type equiv_rule = string * pform * pform * pform * pform
type rules =
    SeqRule of sequent_rule
  | RewriteRule of rewrite_rule
  | EquivRule of equiv_rule
  | ConsDecl of string
type question =
    Implication of pform * pform
  | Inconsistency of pform
  | Frame of pform * pform
  | Equal of pform * args * args
  | Abs of pform
type test =
    TImplication of pform * pform * bool
  | TInconsistency of pform * bool
  | TFrame of pform * pform * pform
  | TEqual of pform * args * args * bool
  | TAbs of pform * pform
val expand_equiv_rules : rules list -> rules list
type inductive_con = {
  con_name : string;
  con_def : pform * string * args list;
}
type inductive = {
  ind_name : string;
  ind_args : args list;
  ind_cons : inductive_con list;
}
type inductive_stmt = IndImport of string | IndDef of inductive
type var = Vars.var
type term = args
type form = pform
val mkVar : var -> term
val mkFun : string -> term list -> term
val mkString : string -> term
val mkFalse : form
val mkEQ : term * term -> form
val mkNEQ : term * term -> form
val mkPPred : string * term list -> form
val mkSPred : string * term list -> form
val mkOr : form * form -> form
val mkStar : form -> form -> form
val mkEmpty : form
val fv_form : pform -> VarSet.t
val ev_form_acc : pform -> VarSet.t -> VarSet.t
val ev_form : pform -> VarSet.t
val string_form : Format.formatter -> form -> unit
val prog_var : string -> var
val fresh_exists_var : unit -> var
type variable_subst = varmap
val empty_subst : variable_subst
val add_subst : var -> term -> variable_subst -> variable_subst
val subst_kill_vars_to_fresh_prog : varset -> variable_subst
val subst_kill_vars_to_fresh_exist : varset -> variable_subst
val subst_form : variable_subst -> form -> form
val mk_seq_rule : psequent * psequent list list * string -> sequent_rule
type external_prover =
    (pform -> pform -> bool) * (pform -> args list -> args list list)
type logic = {
  seq_rules : sequent_rule list;
  rw_rules : rewrite_rule list;
  ext_prover : external_prover;
  consdecl : string list;
}
val empty_logic : logic
