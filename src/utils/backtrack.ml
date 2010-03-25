(********************************************************
   This file is part of jStar 
	src/utils/backtrack.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
exception No_match

let rec find_no_match_simp f l =
  let rec fnm_inner f l =
  match l with 
    [] -> raise No_match
  | x::l -> try f x with No_match -> fnm_inner f l
  in fnm_inner f l 

let rec tryall f l t cont =
  let rec fnm_inner l =
  match l with 
    [] -> raise No_match
  | x::l -> try f x t cont with No_match -> fnm_inner l
  in fnm_inner l 

let andthen first second x cont =
  first x (fun y -> second y cont) 
    

let using x cont f =
  f x cont 
