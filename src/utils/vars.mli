type var =
    PVar of int * string
  | EVar of int * string
  | AnyVar of int * string
val fresh : (int -> 'a -> 'b) -> 'a -> 'b
val freshp_str : string -> var
val freshe_str : string -> var
val fresha_str : string -> var
val freshp : unit -> var
val freshe : unit -> var
val fresha : unit -> var
module StrVarHash :
  sig
    type key = string
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
val concretep_str : StrVarHash.key -> var
val concretee_str : StrVarHash.key -> var
val freshen : var -> var
val pp_var : Format.formatter -> var -> unit
val string_var : var -> string
