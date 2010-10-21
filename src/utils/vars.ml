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


open Format

type var =
  | PVar of int * string
  | EVar of int * string
  | AnyVar of int * string 

let mk_pvar i s = PVar (i, s)
let mk_evar i s = EVar (i, s)
let mk_anyvar i s = AnyVar (i, s)

let gensym = ref 0
let fresh mk s = incr gensym; mk !gensym s
let freshp_str = fresh mk_pvar
let freshe_str = fresh mk_evar
let fresha_str = fresh mk_anyvar
let freshp () = freshp_str "v"
let freshe () = freshe_str "v"
let fresha () = fresha_str "v"

module StrVarHash = 
  Hashtbl.Make(struct 
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let hashcons = StrVarHash.create 1000

let concrete mk vn =
  try StrVarHash.find hashcons vn
  with Not_found ->
    let r = mk 0 vn in
    StrVarHash.add hashcons vn r;
    r

let concretep_str = concrete mk_pvar
let concretee_str = concrete mk_evar

let freshen = function 
  | PVar (_,v) -> freshp_str v
  | EVar (_,v) -> freshe_str v
  | AnyVar (_,v) -> fresha_str v 

let freshen_exists = function 
  | PVar (_,v) 
  | AnyVar (_,v) 
  | EVar (_,v) -> freshe_str v



let pp_var f =
  let p = function 0 -> "" | n -> sprintf "_%d" n in
  function 
    | PVar (n,vn) -> fprintf f "%s%s" vn (p n)
    | EVar (n,vn) -> fprintf f "_%s%s" vn (p n)
    | AnyVar (n,vn) -> fprintf f "a_%s%s" vn (p n)

let string_var = Debug.string_of pp_var
