(********************************************************
   This file is part of jStar 
	src/utils/vars.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano

  $Rev$
  $Version$
  $Id: vars.ml 319 2010-03-25 09:13:01Z mjp41 $

  $LastChangedDate $
  $LastChangedRevision $
*******************************************************************)

type var =
  | PVar of int * string
  | EVar of int * string
  | AnyVar of int * string 

let gensym = ref (0)

let freshe () = 
  gensym := !gensym + 1;
  EVar(!gensym,"v")

let freshp () = 
  gensym := !gensym + 1;
  PVar(!gensym,"v")

let fresha () = 
  gensym := !gensym + 1;
  AnyVar(!gensym,"v")

let freshe_str vn = 
  gensym := !gensym + 1;
  EVar(!gensym,vn)

let freshp_str vn = 
  gensym := !gensym + 1;
  PVar(!gensym,vn)


module StrVarHash = 
  Hashtbl.Make(struct 
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let hashcons = StrVarHash.create 1000


let concretep_str vn = 
  try 
    StrVarHash.find hashcons vn
  with Not_found -> 
    let return = PVar(0,vn) in 
    StrVarHash.add hashcons vn return;
    return

let concretee_str vn = 
  try 
    StrVarHash.find hashcons vn
  with Not_found -> 
    let return = EVar(0,vn) in 
    StrVarHash.add hashcons vn return;
    return


let fresha_str vn = 
  gensym := !gensym + 1;
  AnyVar(!gensym,vn)

let freshen var = 
  match var with 
    PVar (i,v) -> freshp_str v
  | EVar (i,v) -> freshe_str v
  | AnyVar (i,v) -> fresha_str v 




let string_var v =
  let foo n = if n = 0 then Printf.sprintf "" else Printf.sprintf "_%d" n in
  match v with 
    PVar (n,vn) -> Printf.sprintf  "%s%s" vn (foo n)
  | EVar (n,vn) -> Printf.sprintf  "_%s%s" vn (foo n)
  | AnyVar (n,vn) -> Printf.sprintf  "a_%s%s" vn (foo n)

let pp_var ppf v =
  let foo n = if n = 0 then Printf.sprintf "" else Printf.sprintf "_%d" n in
  match v with 
    PVar (n,vn) -> Format.fprintf ppf "%s%s" vn (foo n)
  | EVar (n,vn) -> Format.fprintf ppf "_%s%s" vn (foo n)
  | AnyVar (n,vn) -> Format.fprintf ppf "a_%s%s" vn (foo n)

