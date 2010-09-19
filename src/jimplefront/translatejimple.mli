val curr_static_methodSpecs : Javaspecs.methodSpecs ref
val curr_dynamic_methodSpecs : Javaspecs.methodSpecs ref
val fresh_label : unit -> string
val mk_parameter : int -> Vars.var
val get_static_spec : Jparsetree.signature -> Spec.spec option
val get_dynamic_spec : Jparsetree.signature -> Spec.spec option
val get_spec :
  Jparsetree.invoke_expr -> Spec.spec * Jparsetree.immediate list
val retvar_term : Psyntax.args
val translate_assign_stmt :
  Jparsetree.variable -> Jparsetree.expression -> Core.core_statement
val assert_core : Jparsetree.expression -> Core.core_statement
val jimple_statement2core_statement :
  Jimple_global_types.statement_inner -> Core.core_statement list
exception Contained
val is_init_method : Jimple_global_types.methdec_jimple -> bool
val methdec2signature_str : Jimple_global_types.methdec_jimple -> string
val jimple_stmt_create :
  Core.core_statement -> Printing.source_location option -> Cfg_core.cfg_node
val jimple_stmts2core :
  (Jimple_global_types.statement_inner * Printing.source_location option)
  list -> Cfg_core.cfg_node list
val get_spec_for :
  Jimple_global_types.methdec_jimple ->
  Jimple_global_types.member list -> Jparsetree.class_name -> Spec.spec
val resvar_term : Psyntax.args
val conjoin_with_res_true : Psyntax.pform -> Psyntax.pform
val get_requires_clause_spec_for :
  Jimple_global_types.methdec_jimple ->
  'a -> Jparsetree.class_name -> Spec.spec
val get_dyn_spec_for :
  Jimple_global_types.methdec_jimple ->
  'a -> Jparsetree.class_name -> Spec.spec
module LocalMap :
  sig
    type key = string
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
type local_map = Psyntax.args list Javaspecs.AxiomMap.t
val jimple_locals2stattype_rules :
  Jparsetree.local_var list -> Psyntax.sequent_rule list
val add_static_type_info :
  Psyntax.logic -> Jparsetree.local_var list -> Psyntax.logic
val compute_fixed_point :
  Jimple_global_types.jimple_file ->
  Psyntax.logic ->
  Psyntax.logic -> Javaspecs.methodSpecs -> Javaspecs.methodSpecs -> unit
