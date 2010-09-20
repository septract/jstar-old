(********************************************************
   This file is part of jStar 
	src/utils/multiset.mli
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(* Multiset that allows for iteration through the elements *)

module MultisetImpl (A : Map.OrderedType) :
  sig 
    type t = A.t
    type multiset


(* Checks if the multiset is empty *)
    val is_empty : multiset -> bool 
(* The iterator has more elements *)
    val has_more : multiset -> bool
(* Move to the next element *)
    val next  : multiset -> multiset
(* return the current element, and remove it from the set *)
    val remove : multiset -> t * multiset
(* Restart search in multiset *)
    val restart : multiset -> multiset

(** [MultisetImpl.iter f m] applies function [f] in turn to all the
 * elements of [m] in increasing order. *)
    val iter : (t -> unit) -> multiset -> unit

    val fold : ('a -> t -> 'a) -> 'a -> multiset -> 'a

(* Convert a normal list to this kind of multiset *)
    val lift_list : t list -> multiset
(* union of two multisets, restarts interator of new multiset *)
    val union : multiset -> multiset -> multiset
    val empty : multiset

(* Computes intersection of two multisets, 
   also returns remainders.
   Uses comparison function to improve efficiency *)
    val intersect : multiset -> multiset -> (multiset * multiset * multiset)

    val back : multiset -> int -> multiset

    val map_to_list : multiset -> (A.t -> 'b) -> 'b list
  end

