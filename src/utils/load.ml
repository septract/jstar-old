(********************************************************
   This file is part of jStar 
	src/utils/load.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(* File to read a logic file and its imports. *)
open System

type 'a importoption =
    ImportEntry of string 
  | NormalEntry of 'a


let import_flatten_extra_rules dirs filename extra_rules fileparser = 
  let rec import_flatten_inner dirs filename acc already_included = 
    let rel_dir = (Filename.dirname filename) in
    let filename = 
      try 
	System.find_file_from_dirs dirs filename 
      with Not_found  ->  Format.printf "Cannot find file: %s@\n" filename; raise Exit
    in   
    if List.mem filename already_included then 
      (if !(Debug.debug_ref) then Format.printf "Warning: Double inclusion of file: %s@\n" filename; 
       (acc,already_included)
      )
    else (   
    let already_included = filename::already_included in 
    if !(Debug.debug_ref) then Printf.printf "Start parsing logic in %s...\n" filename;
    let inchan = open_in filename in 
    let file_entry_list  = fileparser (Lexing.from_channel inchan) in 
    close_in inchan;
    if !(Debug.debug_ref) then Printf.printf "Parsed %s!\n" filename;
    List.fold_left
      (fun (acc,already_included) entry -> 
	match entry with 
	  ImportEntry filen -> 
	    import_flatten_inner (rel_dir::dirs) filen acc already_included
	| NormalEntry ent -> 
	    (ent::acc, already_included)	    
      ) (acc,already_included) (extra_rules@file_entry_list)
     )
  in
  fst (import_flatten_inner dirs filename [] [])

let import_flatten dirs filename fileparser = import_flatten_extra_rules dirs filename [] fileparser
