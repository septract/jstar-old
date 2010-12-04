open Ast
open Format

(* TODO: identify common parts ?? *)
(* TODO: first generate an ast for the code, then optimize, then dump *)
(* TODO: get rid of failwith using types *)
(* TODO: eval_<non_def_type> made explicit virtual methods (eg, eval_string) *)
(* TODO: optimize the output (eg, fold_left k d [] -> d) *)
(* TODO: process multiple mli input files *)

let rec list sep p ppf = function
    [] -> ()
  | [x] -> fprintf ppf "%a" p x
  | x::xs -> fprintf ppf "%a%s%a" p x sep (list sep p) xs

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

module EvalClass = struct
  let fresh_id =
    let cnt = ref 0 in
    fun () -> incr cnt; sprintf "_%d" !cnt

  let rec pattern_match h = function
    | (TE_id _ as old)
    | (TE_application ("option", _) as old)
    | (TE_application ("list", _) as old) ->
        let x = fresh_id () in
        Hashtbl.add h x old; TE_id(Id x)
    | TE_tuple ts -> TE_tuple (List.map (pattern_match h) ts)
    | TE_arrow _ -> failwith "todo: preprocess to get rid of 'a->'b types"
    | TE_application _ -> failwith "todo: treat parametrized types"

  let rec pattern ppf = function
    | TE_id(Id "unit") -> fprintf ppf "()"
    | TE_id x -> fprintf ppf "%a" id x
    | TE_tuple [] -> ()
    | TE_tuple ts -> fprintf ppf "(%a)" (list ", " pattern) ts
    | _ -> failwith "first call pattern_match"

  let rec code ppf c =
    let lp ppf =
      let co x = function
        | TE_id y -> 
            fprintf ppf "@,self#eval_%a %s; " id y x
        | TE_application ("option", y) ->
            let nc = Hashtbl.create 7 in
            let p = pattern_match nc y in
            fprintf ppf "@,match %s with@ None -> _d |@ Some %a -> (%a); "
              x pattern p code nc
        | TE_application ("list", y) ->
            let nc = Hashtbl.create 7 in
            let p = pattern_match nc y in
            fprintf ppf "@,List.fold_left@ self#combine@ _d@ (List.map@ (fun %a ->@ %a)@ %s);" 
              pattern p code nc x
        | _ -> failwith "todo" in
      Hashtbl.iter co in
    fprintf ppf "List.fold_left@ self#combine@ _d@ [%a]" lp c

  let constructor ppf (c, te) =
    let b = Hashtbl.create 7 in
    let p = pattern_match b te in
    fprintf ppf "@\n@[<4>| %s %a ->@ %a@]" c pattern p code b

  let type_kind n ppf = function
      TK_abstract -> ()
    | TK_variant [] -> failwith "empty variant: check parser"
    | TK_variant cs ->
        fprintf ppf "@[<2>method eval_%s = function" n;
        fprintf ppf "%a" (list "" constructor) cs;
        fprintf ppf "@]"
    | TK_synonym t ->
        let c = Hashtbl.create 7 in
        let p = pattern_match c t in
        fprintf ppf "@[<2>method eval_%s %a =@ %a@]" n pattern p code c

  let ml_type ppf {type_name=n; type_kind=k} =
    fprintf ppf "@\n%a" (type_kind n) k

  let print ast =
    let ppf = std_formatter in
    fprintf ppf "@[@[<2>class virtual ['a] evaluator _d = object (self)";
    fprintf ppf "%a" (list "" ml_type) ast;
    fprintf ppf "@\nmethod virtual combine : 'a -> 'a -> 'a";
    fprintf ppf "@]@\nend@."
end

module Code = struct
  let print _ = ()
end
