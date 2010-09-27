exception No_match
val find_no_match_simp : ('a -> 'b) -> 'a list -> 'b
val tryall : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b -> 'c -> 'd
val andthen : ('a -> ('b -> 'c) -> 'd) -> ('b -> 'e -> 'c) -> 'a -> 'e -> 'd
val using : 'a -> 'b -> ('a -> 'b -> 'c) -> 'c
