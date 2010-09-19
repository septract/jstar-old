exception Class_defines_external_spec
val append_rules :
  Psyntax.logic -> Psyntax.sequent_rule list -> Psyntax.logic
val same_elements : 'a list -> bool
val apf :
  string -> Vars.var -> (string * Psyntax.args) list -> Psyntax.pform_at list
val apf_match : string -> Vars.var -> Vars.var -> Psyntax.pform_at list
val not_null1 : Psyntax.args -> Psyntax.pform_at list
val not_null : Vars.var -> Psyntax.pform_at list
exception BadAPF of string
val add_apf_to_logic :
  Psyntax.logic ->
  (string * Psyntax.VarMap.key * (string * Psyntax.args) list *
   Psyntax.pform * 'a)
  list -> string -> Psyntax.logic
val augmented_logic_for_class :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val parent_relation :
  Spec_def.class_spec list ->
  (Jparsetree.class_name * Jparsetree.class_name) list
val remove_duplicates : 'a list -> 'a list
val transitive_closure : ('a * 'a) list -> ('a * 'a) list
val topological_sort : ('a * 'a) list -> 'a list
val a_topological_ordering_of_all_classes :
  Spec_def.class_spec list -> Jparsetree.class_name list
val parent_classes_and_interfaces :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Jparsetree.class_name list
val rules_for_implication :
  string * Psyntax.pform * Psyntax.pform ->
  Psyntax.pform -> Psyntax.sequent_rule list
val logic_with_where_pred_defs :
  (string * Psyntax.VarMap.key list * Psyntax.pform) list ->
  Psyntax.logic -> Psyntax.logic
val logic_and_implications_for_exports_verification :
  Jparsetree.class_name ->
  Spec_def.class_spec list ->
  Psyntax.logic -> Psyntax.logic * Spec_def.named_implication list
val add_exported_implications_to_logic :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
module AxiomMap :
  sig
    type key = Jparsetree.class_name * string
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
type axiom_map = (Psyntax.pform * Psyntax.pform) AxiomMap.t
val filtermap : ('a -> bool) -> ('a -> 'b) -> 'a list -> 'b list
val axiommap_filter :
  (AxiomMap.key -> 'a -> bool) -> 'a AxiomMap.t -> 'a AxiomMap.t
val axiommap2list : (AxiomMap.key -> 'a -> 'b) -> 'a AxiomMap.t -> 'b list
val spec_file_to_axiom_map :
  Spec_def.class_spec list -> (Psyntax.pform * Psyntax.pform) AxiomMap.t
val implications_for_axioms_verification :
  Jparsetree.class_name ->
  (Psyntax.pform * Psyntax.pform) AxiomMap.t ->
  Spec_def.named_implication list
module AxiomMap2 :
  sig
    type key = Jparsetree.class_name
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
type axiom_map2 = Spec_def.named_implication list AxiomMap2.t
val spec_file_to_axiom_map2 :
  Spec_def.class_spec list -> Spec_def.named_implication list AxiomMap2.t
val add_axiom_implications_to_logic :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val is_interface : Jparsetree.class_name -> Spec_def.class_spec list -> bool
val is_method_abstract :
  Jparsetree.method_signature -> Spec_def.class_spec list -> bool
module MethodMap :
  sig
    type key = Jparsetree.method_signature
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
module MethodMapH :
  sig
    val filter :
      (MethodMap.key -> 'a -> bool) -> 'a MethodMap.t -> 'a MethodMap.t
  end
module MethodSet :
  sig
    type elt = Jparsetree.method_signature
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
type methodSpecs = (Spec.spec * Printing.source_location option) MethodMap.t
val emptyMSpecs : methodSpecs
val addMSpecs :
  MethodMap.key ->
  Spec.spec * Printing.source_location option ->
  (Spec.spec * Printing.source_location option) MethodMap.t -> methodSpecs
val spec_list_to_spec : Spec.spec list -> Spec.spec
val class_spec_to_ms :
  Spec_def.class_spec ->
  methodSpecs * methodSpecs -> methodSpecs * methodSpecs
val remove_this_type_info : Psyntax.pform_at list -> Psyntax.pform_at list
val static_to_dynamic : Spec.spec -> Spec.spec
val filtertype_spat : string -> Psyntax.pform_at -> Psyntax.pform_at
val filtertype : string -> Psyntax.pform -> Psyntax.pform
val filterdollar_at : Psyntax.pform_at -> Psyntax.pform_at
val filterdollar : Psyntax.pform -> Psyntax.pform
val dynamic_to_static : string -> Spec.spec -> Spec.spec
val filter_dollar_spec : Spec.spec -> Spec.spec
val fix_spec_inheritance_gaps :
  Jparsetree.class_name list ->
  ('a * 'b) MethodMap.t ->
  Spec_def.class_spec list ->
  (Jparsetree.class_name * Jparsetree.j_type * Jparsetree.name *
   Jparsetree.parameter list -> bool) ->
  string -> ('a * 'b) MethodMap.t
val fix_gaps :
  (Spec.spec * 'a) MethodMap.t * (Spec.spec * 'a) MethodMap.t ->
  Spec_def.class_spec list ->
  (Spec.spec * 'a) MethodMap.t * (Spec.spec * 'a) MethodMap.t
val spec_file_to_method_specs :
  Spec_def.class_spec list -> methodSpecs * methodSpecs
val mk_subeq : Vars.var * Vars.var -> Psyntax.pform_at list
val mk_sub : Vars.var * Vars.var -> Psyntax.pform_at list
val add_common_apf_predicate_rules :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val add_subtype_and_objsubtype_rules :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val refinement_this :
  Psyntax.logic -> Spec.spec -> Spec.spec -> Jparsetree.class_name -> bool
