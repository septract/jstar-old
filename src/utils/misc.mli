val map_option : ('a -> 'b option) -> 'a list -> 'b list
val map_lift_exists : ('a -> 'b option) -> 'a list -> 'b list option
val map_lift_forall : ('a -> 'b option) -> 'a list -> 'b list option
type ('a, 'b) sum = Inr of 'a | Inl of 'b
val map_sum : ('a -> ('b, 'c) sum) -> 'a list -> 'c list * 'b list
val remove_duplicates : ('a -> 'a -> int) -> 'a list -> 'a list
val intcmp : 'a -> 'a -> int
val intcmp2 : 'a * 'b -> 'a * 'b -> int
val find_no_match_simp : ('a -> 'b) -> 'a list -> 'b
val lift_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b
val lift_option : ('a -> 'b option) -> 'a option -> 'b option
val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
val inter_list : int -> int -> int list
val add_index : 'a list -> int -> ('a * int) list
module MapHelper :
  functor (M : Map.S) ->
    sig val filter : (M.key -> 'a -> bool) -> 'a M.t -> 'a M.t end
