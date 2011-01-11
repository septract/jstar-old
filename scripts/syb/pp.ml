(* TODO Deprecate most of it. *)

open Ast
open Format

let rec list sep p ppf = function
    [] -> ()
  | [x] -> fprintf ppf "%a" p x
  | x::xs -> fprintf ppf "%a%s%a" p x sep (list sep p) xs

let string ppf s = fprintf ppf "%s" s

let rec id ppf = function
    Id s -> fprintf ppf "%s" s
  | Dot (s, t) -> fprintf ppf "%a.%s" id s t

module Ast = struct 
  let rec type_expr ppf = function
      TE_id x -> 
        fprintf ppf "%a" id x
    | TE_application (x, t) -> 
        fprintf ppf "@[%a %s@]" type_expr t x
    | TE_tuple ts ->
        fprintf ppf "@[%a@]" (list " * " type_expr) ts
    | TE_arrow (t, s) ->
        fprintf ppf "@[%a -> %a@]" type_expr t type_expr s

  let constructor ppf = function
      (c, TE_tuple []) -> fprintf ppf "%s" c
    | (c, t) -> fprintf ppf "%s of @[%a@]" c type_expr t

  let type_kind ppf = function
      TK_abstract -> fprintf ppf "= <abs>"
    | TK_variant [] -> failwith "empty variant: check parser"
    | TK_variant cs -> fprintf ppf "= %a" (list " | " constructor) cs
    | TK_synonym t -> fprintf ppf "= %a" type_expr t

  let ml_type ppf {type_name=type_name; type_kind=k} =
    fprintf ppf "@[<2>type %s@ %a@." type_name type_kind k

  let print = List.iter (ml_type std_formatter)
end
