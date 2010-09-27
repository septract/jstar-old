type ntype = Plain | Good | Error | Abs | UnExplored
type id = int
val file : string ref
val set_group : bool -> unit
type node = {
  mutable content : string;
  id : id;
  mutable ntype : ntype;
  mutable url : string;
  mutable edges : edge list;
  cfg : Cfg_core.cfg_node option;
}
and edge = string * string * node * node * string option
val mk_node :
  string ->
  id -> ntype -> string -> edge list -> Cfg_core.cfg_node option -> node
module Idmap :
  sig
    type key = int option
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
val pp_dotty_transition_system : unit -> unit
type formset_entry = Sepprover.inner_form * node
type formset = formset_entry list
type formset_hashtbl = (int, formset) Hashtbl.t
val parameter : int -> string
exception Contained
val verify :
  string ->
  Cfg_core.cfg_node list ->
  Spec.spec -> Psyntax.logic -> Psyntax.logic -> bool
val verify_ensures :
  string ->
  Cfg_core.cfg_node list ->
  Psyntax.pform ->
  (Psyntax.pform -> Psyntax.form) ->
  Sepprover.inner_form list list -> Psyntax.logic -> Psyntax.logic -> unit
val get_frame :
  Cfg_core.cfg_node list ->
  Psyntax.pform ->
  Psyntax.logic -> Psyntax.logic -> Sepprover.inner_form list
