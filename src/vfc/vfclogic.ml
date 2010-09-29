(* Verified Featherweight C logic support *)

open VfcAST
open Psyntax


(* location denotation; will reduce to pointer arithmetic with rewrite rules *)
let mk_loc x fo = 
  match fo with
    | Some f_id -> mkFun "loc" [x; mkString f_id]
    | None -> mkFun "loc" [x]

(* create x |={p}=>_h^{T} e *)
let mk_multiheap_blob h t p x e = mkSPred("blob", [h; t; p; x; e])

let host_heap = mkString "host"
let local_heap = mkString "local"

let full_perm = mkFun "ptop" []
let no_perm = mkFun "pbot" []

let mk_type (t : vfc_type) =
  let rec type_string t =
    match t with
    | Bool -> "bool"
    | Byte -> "byte"
    | Int -> "int"
    | Struct s_id -> "^" ^ s_id
    | Pointer tt -> "*" ^ (type_string tt)
    | Void_ptr -> "*void"
    | Thread_ptr -> "*thread"
    | Array (tt, sz) -> "[" ^ (string_of_int sz) ^ "]" ^ (type_string tt) 
  in
  mkString (type_string t)

let mk_local_blob t x e = mk_multiheap_blob local_heap t full_perm x e
let mk_host_blob t x e = mk_multiheap_blob host_heap t full_perm x e
