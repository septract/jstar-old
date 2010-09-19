val map_option : ('a -> 'b option) -> 'a list -> 'b list
type ('a, 'b) sum = Inr of 'a | Inl of 'b
val remove_duplicates : ('a -> 'a -> int) -> 'a list -> 'a list
val intcmp : 'a -> 'a -> int
val intcmp2 : 'a * 'b -> 'a * 'b -> int
val find_no_match_simp : ('a -> 'b) -> 'a list -> 'b
val lift_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b
val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
val add_index : 'a list -> int -> ('a * int) list
module MapHelper :
  functor (M : Map.S) ->
    sig val filter : (M.key -> 'a -> bool) -> 'a M.t -> 'a M.t end
