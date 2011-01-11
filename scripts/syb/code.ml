open Format
open Std
(* types {{{ *)
type pattern =
  | P_var of string
  | P_tuple of pattern list
  | P_const of string * pattern list
type value =
  | V_var of string
  | V_list of value list
  | V_tuple of value list
  | V_const of string * value list
  | V_app of value * value
  | V_abs of (pattern * value) list
type meth_d = {
  mt_name : string;
  mt_type : Ast.type_expr;
  mt_body : value option
}
type cl_ss = {
  c_name : string;
  c_type_vars : StringSet.t;
  c_arguments : string list;
  c_methods : meth_d StringMap.t
}
type modul_ = {
  md_opens : StringSet.t;
  md_classes : cl_ss StringMap.t
}
(* types }}} *)
(* sanity checks {{{ *)
let check_unique xs =
  let set_of_list xs = List.fold_right StringSet.add xs StringSet.empty in
  assert (StringSet.cardinal (set_of_list xs) = List.length xs)
let check_method _ = ()
let check_class {c_name=_; c_type_vars=_; c_methods=ms; c_arguments=args} =
  check_unique args;
  let cm mn m = assert (mn = m.mt_name); check_method m in
  StringMap.iter cm ms
let check_module {md_opens=os; md_classes=cs} =
  let cc cn c = assert (cn = c.c_name); check_class c in
  StringMap.iter cc cs

(* sanity checks }}} *)
(* pretty print {{{ *)
let lgt2 = function
  | _ :: _ -> true
  | _ -> false

(* NOTE high to low precedences: application, comma, semicolon, abstraction. *)

let p1 = function (* precedence of outer op *)
  | V_const (_, (_::_)) | V_app _ -> 40
  | V_abs _ -> 10
  | _ -> 100

let p2 = function (* precedence of inner op *)
  | V_app _ -> 40
  | V_const (_, [_]) -> 40
  | V_const (_, (_::_::_)) -> 30
  | V_list (_::_::_) -> 20
  | _ -> 0

let rec pp_pattern ppf = function
  | P_var s -> 
      fprintf ppf "%s@," s
  | P_tuple ps -> 
      fprintf ppf "@[%a@]@," (Pp.list ", " pp_pattern) ps
  | P_const (c, ps) ->
      fprintf ppf "%s" c;
      (match ps with
        | [] -> ()
        | [p] -> fprintf ppf " %a" pp_pattern p
        | ps -> fprintf ppf "(%a)" (Pp.list ", " pp_pattern) ps)

let pp_one_abs r ppf (p, v) =
  fprintf ppf "@[%a ->@ %a@]@," pp_pattern p r v
let pp_value'' r ppf = function
  | V_var s -> fprintf ppf "%s" s
  | V_list vs -> fprintf ppf "[%a]" (Pp.list "; " r) vs
  | V_tuple vs -> fprintf ppf "(%a)" (Pp.list ", " r) vs
  | V_const (c, []) -> fprintf ppf "%s" c
  | V_const (c, [v]) -> fprintf ppf "%s %a" c r v
  | V_const (c, vs) -> fprintf ppf "%s (%a)" c (Pp.list ", " r) vs
  | V_app (a, b) -> fprintf ppf "%a %a" r a r b
  | V_abs xs -> fprintf ppf "function@ %a" (Pp.list "| " (pp_one_abs r)) xs

let rec pp_value' p ppf x =
  let pp = pp_value'' (pp_value' (p2 x)) in
  if p1 x <= p then
    fprintf ppf "@[(%a)@]@," pp x
  else
    fprintf ppf "@[%a@]@," pp x

let pp_value = pp_value' 0

let pp_method ppf _ {mt_name=n; mt_type=t; mt_body=b} =
  match b with
    | None -> 
        fprintf ppf "@\n@[<2>method virtual %s : %a@]" n Pp.Ast.type_expr t
    | Some b ->
        fprintf ppf "@\n@[<2>method %s : %a =@ %a@]" 
          n Pp.Ast.type_expr t pp_value b

let pp_class ppf {c_name=n; c_type_vars=ts; c_arguments=args; c_methods=ms} =
  let v =
    if StringMap.fold (fun _ m v -> v || m.mt_body = None) ms false
    then " virtual" else "" in
  let ts = StringSet.elements ts in
  let pp_ts ppf = function
    | [] -> ()
    | ts -> fprintf ppf " [%a]" (Pp.list "," Pp.string) ts in 
  fprintf ppf "@[@[<2>class%s%a %s = " v pp_ts ts n;
  if args <> [] then fprintf ppf "fun %a -> " (Pp.list " " Pp.string) args;
  fprintf ppf "object(self)";
  StringMap.iter (pp_method ppf) ms;
  fprintf ppf "@]@\nend@\n@]"

let pp_module ppf {md_opens=os; md_classes=cs} =
  let os = StringSet.elements os in
  let cs = StringMap.fold (fun _ v vs -> v :: vs) cs [] in
  let pp_o ppf s = fprintf ppf "open %s@\n" s in
  fprintf ppf "@[%a@\n%a@]" (Pp.list "" pp_o) os (Pp.list "" pp_class) cs
(* pretty print }}} *)
