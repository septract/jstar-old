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
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
  end
type varset = VarSet.t
val vs_mem : VarSet.elt -> VarSet.t -> bool
val vs_add : VarSet.elt -> VarSet.t -> VarSet.t
val vs_empty : VarSet.t
val vs_fold : (VarSet.elt -> 'a -> 'a) -> VarSet.t -> 'a -> 'a
val vs_iter : (VarSet.elt -> unit) -> VarSet.t -> unit
val vs_diff : VarSet.t -> VarSet.t -> VarSet.t
val vs_exists : (VarSet.elt -> bool) -> VarSet.t -> bool
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
val vm_add : VarMap.key -> 'a -> 'a VarMap.t -> 'a VarMap.t
val vm_empty : 'a VarMap.t
val vm_find : VarMap.key -> 'a VarMap.t -> 'a
val vm_mem : VarMap.key -> 'a VarMap.t -> bool
val vm_is_empty : 'a VarMap.t -> bool
module VarHash :
  sig
    type key = Vars.var
    type 'a t
    val create : int -> 'a t
    val clear : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
  end
type varhashargs = args VarHash.t
type 'a varhash_t = 'a VarHash.t
val vh_create : int -> 'a VarHash.t
val vh_add : 'a VarHash.t -> VarHash.key -> 'a -> unit
val vh_find : 'a VarHash.t -> VarHash.key -> 'a
type varmap = Plain of varmapargs | Freshen of varmapargs * varhashargs
val find : VarMap.key -> varmap -> args
val add : VarMap.key -> args -> varmap -> varmap
val empty : varmap
val freshening_subs : varmap -> varmap
val subst_var : varmap -> VarMap.key -> args
val subst_args : varmap -> args -> args
val string_args : Format.formatter -> args -> unit
val string_args_list : Format.formatter -> args list -> unit
val string_args_fldlist : Format.formatter -> (string * args) list -> unit
val fv_args : args -> VarSet.t -> VarSet.t
val fv_args_list : args list -> VarSet.t -> VarSet.t
val fv_fld_list : (string * args) list -> VarSet.t -> VarSet.t
val ev_args : args -> VarSet.t -> VarSet.t
val ev_args_list : args list -> VarSet.t -> VarSet.t
val ev_fld_list : (string * args) list -> VarSet.t -> VarSet.t
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
val isFalse : pform_at list -> bool
val pconjunction : pform -> pform -> pform
val ( &&& ) : pform -> pform -> pform
val pwand : pform -> pform -> pform_at list
val mkGarbage : pform_at list
val mkWand : pform * pform -> pform_at list
val mkSeptract : pform * pform -> pform
val subst_pform_at : varmap -> pform_at -> pform
val subst_pform : varmap -> pform -> pform
val string_varlist : Vars.var list -> string
val string_form_at : Format.formatter -> pform_at -> unit
val fv_form_at : pform_at -> VarSet.t -> VarSet.t
val closes : 'a VarMap.t -> pform -> bool
val ev_form_at : pform_at -> VarSet.t -> VarSet.t
type psequent = pform * pform * pform
val fv_psequent : pform * pform * pform -> VarSet.t
val subst_psequent : varmap -> pform * pform * pform -> pform * pform * pform
val purify : pform_at list -> pform_at list
type varterm = Var of varset
type where = NotInContext of varterm | NotInTerm of varterm * args
val string_vs : Format.formatter -> VarSet.t -> unit
val string_where : Format.formatter -> where -> unit
type sequent_rule =
    psequent * psequent list list * string * (pform * pform) * where list
val pp_entailment : Format.formatter -> pform * pform -> unit
val pp_psequent : Format.formatter -> psequent -> unit
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
val prog_var : Vars.StrVarHash.key -> var
val exists_var : Vars.StrVarHash.key -> var
val fresh_exists_var : unit -> var
val fresh_unify_var : unit -> var
val fresh_prog_var : unit -> var
val fresh_exists_var_str : string -> var
val fresh_prog_var_str : string -> var
val unify_var : string -> var
type term = args
val mkVar : var -> term
val mkFun : string -> term list -> term
val mkString : string -> term
type form = pform
val mkFalse : form
val mkNEQ : term * term -> form
val mkEQ : term * term -> form
val mkPPred : string * term list -> form
val mkSPred : string * term list -> form
val mkOr : form * form -> form
val mkStar : form -> form -> form
val mkEmpty : form
val fv_form_acc : pform -> VarSet.t -> VarSet.t
val fv_form : pform -> VarSet.t
val ev_form_acc : pform -> VarSet.t -> VarSet.t
val ev_form : pform -> VarSet.t
val string_form : Format.formatter -> form -> unit
type variable_subst = varmap
val empty_subst : variable_subst
val add_subst : var -> term -> variable_subst -> variable_subst
val freshening_subst : variable_subst -> variable_subst
val subst_kill_vars_to_fresh_prog : varset -> variable_subst
val subst_kill_vars_to_fresh_exist : varset -> variable_subst
val subst_freshen_vars : varset -> variable_subst
val subst_form : variable_subst -> form -> form
val mk_seq_rule : psequent * psequent list list * string -> sequent_rule
type external_prover =
    (pform -> pform -> bool) * (pform -> args list -> args list list)
val default_pure_prover : external_prover
type logic = {
  seq_rules : sequent_rule list;
  rw_rules : rewrite_rule list;
  ext_prover : external_prover;
  consdecl : string list;
}
val empty_logic : logic
