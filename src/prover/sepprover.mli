module SepProver :
  sig
    val debug : bool -> unit
    type var 
    val prog_var : string -> var
    val exists_var : string -> var
    val fresh_exists_var : unit -> var
    val fresh_unify_var : unit -> var
    val fresh_prog_var : unit -> var
    val fresh_exists_var_str : string -> var
    val fresh_prog_var_str : string -> var
    val unify_var : string -> var
    type term 
    val mkVar : var -> term
    val mkFun : string -> term list -> term
    val mkString : string -> term
    type form 
    val mkFalse : form
    val mkNEQ : term * term -> form
    val mkEQ : term * term -> form
    val mkPPred : string * term list -> form
    val mkSPred : string * term list -> form
    val mkOr : form * form -> form
    val mkStar : form -> form -> form
    val mkEmpty : form
    type varset 
    val vs_mem : var -> varset -> bool
    val vs_add : var -> varset -> varset
    val vs_empty : varset
    val vs_fold : (var -> 'a -> 'a) -> varset -> 'a -> 'a
    val vs_iter : (var -> unit) -> varset -> unit
    val vs_diff : varset -> varset -> varset
    val vs_exists : (var -> bool) -> varset -> bool
    val fv_form : form -> varset
    val ev_form : form -> varset
    val string_form : Format.formatter -> form -> unit
    type var_subst
    val empty_subst : var_subst
    val add_subst : var -> term -> var_subst -> var_subst
    val freshening_subst : var_subst -> var_subst
    val subst_kill_vars_to_fresh_prog : varset -> var_subst
    val subst_kill_vars_to_fresh_exist : varset -> var_subst
    val subst_freshen_vars : varset -> var_subst
    val subst_form : var_subst -> form -> form
    type rform 
    val convert : form -> rform
    val conjoin : form -> rform -> rform
    val kill_var : var -> rform -> unit
    val update_var_to : var -> term -> rform -> unit
    val form_clone : rform -> rform
    type logic 
    type sequent = form * form * form
    type rewrite_rule = {
      op : string;
      arguments : term list;
      new_term : term;
      rule_name : string;
    }
    type sequent_rule = {
      conclusion : sequent;
      premises : sequent list list;
      name : string;
      without : form;
    }
    val empty_logic : logic
    val add_rewrite_rule : rewrite_rule -> logic -> logic
    val add_sequent_rule : sequent_rule -> logic -> logic
    val implies : logic -> rform -> rform -> bool
    val frame : logic -> rform -> form -> rform list
  end
