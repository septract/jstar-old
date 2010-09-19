(********************************************************
   This file is part of jStar 
	src/utils/misc.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
open Backtrack 

let map_option f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el  with
	None -> rest
   |	Some el -> el::rest) l []

let map_lift_exists f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el, rest  with
	None,_ -> rest
   |	Some el,Some rest -> Some (el::rest)
   |  Some el, None -> Some [el]) l None

let map_lift_forall f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el, rest  with
     	  None,_ -> None
	    | _, None -> None
      |	Some el,Some rest -> Some (el::rest)) l (Some [])


type ('a,'b) sum = 
    Inr of 'a
  | Inl of 'b

let map_sum f l
    =
  List.fold_right
    (fun el (restl,restr) -> 
      match f el with
      | Inl l -> (l::restl,restr)
      | Inr r -> (restl,r::restr)) l ([],[])


let remove_duplicates c l =
  let l = List.sort c l in 
  snd (
  List.fold_left 
    (fun (complast,list) next  ->
      if complast next = 0 then (complast,list) else (c next, next::list)
	) ((fun _ -> -1),[]) l
    )

let intcmp a b =
  if a<b then -1 else if a=b then 0 else 1

let intcmp2 (x1,x2) (y1,y2) =
  let v = intcmp x1 y1 in 
  if v = 0 then intcmp x2 y2 
  else v


let rec find_no_match_simp f l =
  let rec fnm_inner f l =
  match l with 
    [] -> raise No_match
  | x::l -> try f x with No_match -> fnm_inner f l
  in fnm_inner f l 



let lift_pair f = 
  fun (x,y) -> (f x, f y)

let lift_option f =
  fun x -> match x with
    Some x -> f x
  | None -> None

(* Similar to the one in Haskell. *)
let curry f a b = f (a, b)
    
let rec inter_list (i : int) (j : int) : int list =  
  if i > j then [] else (i :: inter_list (i+1) j) 


let rec add_index 
    ( xs : 'a list ) 
    ( i : int ) : ('a * int) list = 
  match xs with  | []     ->  [] 
                 | y::ys  ->  ( (y,i) :: (add_index ys (i+1)) ) 

(* TODO(rgrig): This module should go away when we move to ocaml 3.12.
 *
 * A few helpers for dealing with maps. This is a workaround for the lack of
 * some functions in the standard Map.S module. Whenever you define a map
 * [module M = Map.Make (...)] you can also define [module MH = MapHelper (M)].
 * Normal functions like [M.fold] are used as before, but you can also say
 * things like [MH.filter].
 *
 * If you tend o repeat yourself when dealing with Maps, then please consider
 * adding a function here.
 *)
module MapHelper = functor (M : Map.S) -> struct
  (* The running time is O(m+n lg n), where m is the size of map and n the size
   * of the result. It is possible in principle to achieve O(m), but the Map.S
   * interface makes it hard/impossible. *)
  let filter (p : M.key -> 'a -> bool) (map : 'a M.t) : 'a M.t =
    M.fold (fun k v a -> if p k v then M.add k v a else a) map M.empty
end
