(** code generator *)

open Ast
open Format
open Std

(* TODO: collect mentioned but unused types, add them as abstract *)
(* TODO: collect module names, strip types *)

let modules = ref StringSet.empty
let evaluators = ref StringMap.empty
let mentioned_types = ref StringSet.empty

let last_var = ref 0
let fresh_var () = incr last_var; sprintf "_%d" !last_var

let id = 
  let v s = 
    mentioned_types := StringSet.add s !mentioned_types;
    Code.V_var (sprintf "self#eval_%s" s) in
  function
    | Id s -> v s
    | Dot (m, s) -> modules := StringSet.add (id2str m) !modules; v s

let v x = Code.V_var x

let mk_abs = function 
  | [] -> failwith "Code.V_abs must have a non-empty list"
  | [Code.P_var x, Code.V_app(f, Code.V_var y)] when x = y -> f
  | xs -> (* TODO: optimize when the pattern isn't used *)
      if List.for_all (fun (_, w) -> w = v Code.default) xs then
        Code.V_abs [Code.P_var "_", v Code.default]
      else
        Code.V_abs xs

let mk_app fs v = 
  let rec substitute x v = function
    | Code.V_var y when x = y -> v
    | Code.V_var y as vy -> vy
    | Code.V_list vs -> Code.V_list (List.map (substitute x v) vs)
    | Code.V_const (c, vs) -> Code.V_const (c, List.map (substitute x v) vs)
    | Code.V_app (a, b) -> Code.V_app (substitute x v a, substitute x v b)
    | Code.V_abs xs ->
        let rec binds = function
          | Code.P_var y when x = y -> true
          | Code.P_tuple ps
          | Code.P_const (_, ps) -> List.exists binds ps
          | _ -> false in
        let f (p, w) =
          (p, if binds p then w else substitute x v w) in
        mk_abs (List.map f xs) in 
  let app f v = match f with
    | Code.V_abs [Code.P_var x, t] -> substitute x v t
    | _ -> Code.V_app(f, v) in
  match fs with
  | [] -> failwith "internal error"
  | f::fs -> app (List.fold_left app f fs) v

let mk_combine = function
  | Code.V_list [] -> v Code.default
  | Code.V_list [v] -> v
  | (Code.V_list _ as x)
  | (Code.V_app _ as x) -> 
      mk_app [v"List.fold_left"; v"self#combine"; v Code.default] x
  | _ -> failwith "you're trying to combine a non-list"

let mk_map f = function
  | Code.V_list [] -> Code.V_list []
  | Code.V_list [v] -> Code.V_list [mk_app [f] v]
  | (Code.V_list _ as x)
  | (Code.V_app _ as x) 
  | (Code.V_var _ as x) -> mk_app [v"List.map"; f] x
  | _ -> failwith "you're trying to map over a non-list"

let rec mk_abs_te t = mk_abs (type_expr t)

and type_expr = function
  | TE_id t -> 
      let x = fresh_var () in 
      [(Code.P_var x, Code.V_app ((id t), Code.V_var x))]
  | TE_application ("option", t) -> [
      (Code.P_const ("None", []), v Code.default);
      let x = fresh_var () in
      (Code.P_const ("Some", [Code.P_var x]), mk_app [mk_abs_te t] (v x))]
  | TE_application ("list", t) ->
      let x = fresh_var () in
      [Code.P_var x, mk_combine (mk_map (mk_abs_te t) (v x))]
  | TE_tuple ts ->
      let f t =
        let x = fresh_var () in
        (Code.P_var x, mk_app [mk_abs_te t] (v x)) in
      let ps, vs = List.split (List.map f ts) in
      [(Code.P_tuple ps, mk_combine (Code.V_list vs))]
  | _ -> failwith "todo: get rid of function types"

let constructor (c, t) =
  last_var := 0;
  let f = function
    | Code.P_tuple ps -> Code.P_const (c, ps)
    | p -> Code.P_const (c, [p]) in
  List.map (function (a, b) -> f a, b) (type_expr t)

let type_kind = function
    TK_abstract -> None
  | TK_variant cs -> Some (mk_abs (List.concat (List.map constructor cs)))
  | TK_synonym t -> last_var := 0; Some (mk_abs_te t)

let ml_type {type_name=n; type_kind=k} =
  evaluators := StringMap.add n (type_kind k) !evaluators

let default_fun = mk_abs [Code.P_var "_", v Code.default]

let process ast =
  modules := StringSet.empty;
  evaluators := StringMap.empty;
  mentioned_types := StringSet.empty;
  List.iter ml_type ast;
  StringSet.iter (fun t -> if not (StringMap.mem t !evaluators) then
    evaluators := StringMap.add t (Some default_fun) !evaluators) 
    !mentioned_types;
  {Code.modules = !modules; Code.evaluators = !evaluators}
