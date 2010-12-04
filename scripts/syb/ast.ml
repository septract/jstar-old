open Std

type id = Id of string | Dot of id * string
type type_expr =
    TE_id of id
  | TE_application of string * type_expr
  | TE_tuple of type_expr list
  | TE_arrow of type_expr * type_expr
type type_kind =
    TK_abstract
  | TK_variant of (string * type_expr) list
  | TK_synonym of type_expr
type ml_type = {type_name:string; type_kind:type_kind}
type ast = ml_type list

let rec id2str = function
  | Id s -> s
  | Dot (m, s) -> id2str m ^ "." ^ s

(** Asserts that no id appears with more than one module prefix.
  Reports the offenders. *)
let check_name_conflicts ast =
  let add s k v =
    let vs = try StringMap.find k s with Not_found -> StringSet.empty in
    StringMap.add k (StringSet.add v vs) s in
  let rec id acc = function
    | Id s -> add acc s ""
    | Dot (m, s) -> add acc s (id2str m) in
  let rec type_expr acc = function
    | TE_id s -> id acc s
    | TE_application (_, t) -> type_expr acc t
    | TE_tuple ts -> List.fold_left type_expr acc ts
    | TE_arrow (a, b) -> type_expr (type_expr acc a) b in
  let ml_type acc {type_name=_; type_kind=k} = match k with
    | TK_abstract -> acc
    | TK_variant vs -> List.fold_left (fun acc (_, t) -> type_expr acc t) acc vs
    | TK_synonym t -> type_expr acc t in
  let check x ms =
    let sset2str s = "[" ^ StringSet.fold (fun x s -> x^" "^s) s "" ^ "]" in
    if StringSet.cardinal ms > 1 then 
      failwith ("x appears in " ^ sset2str ms) in
  StringMap.iter check (List.fold_left ml_type StringMap.empty ast)

