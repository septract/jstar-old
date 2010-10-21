(********************************************************
   This file is part of jStar
        src/jimplefront/javaspecs.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val append_rules :
  Psyntax.logic -> Psyntax.sequent_rule list -> Psyntax.logic
val apf :
  string -> Vars.var -> (string * Psyntax.args) list -> Psyntax.pform_at list
val augmented_logic_for_class :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val remove_duplicates : 'a list -> 'a list
val parent_classes_and_interfaces :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Jparsetree.class_name list
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
val add_axiom_implications_to_logic :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val is_interface : Jparsetree.class_name -> Spec_def.class_spec list -> bool
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
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
  end
type methodSpecs = (Spec.spec * Printing.source_location option) MethodMap.t
val emptyMSpecs : methodSpecs
val spec_list_to_spec : Spec.spec list -> Spec.spec
val spec_file_to_method_specs :
  Spec_def.class_spec list -> methodSpecs * methodSpecs
val add_common_apf_predicate_rules :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val add_subtype_and_objsubtype_rules :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val refinement_this :
  Psyntax.logic -> Spec.spec -> Spec.spec -> Jparsetree.class_name -> bool
