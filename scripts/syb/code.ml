open Format
open Std

type pattern =
  | P_var of string
  | P_tuple of pattern list
  | P_const of string * pattern list
type value =
  | V_var of string
  | V_list of value list
  | V_const of string * value list
  | V_app of value * value
  | V_abs of (pattern * value) list
type code = {
  modules : StringSet.t; 
  evaluators : value option StringMap.t;
}

let default = "default_value"

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
  | V_const (c, ((_::_) as vs)) -> fprintf ppf "%s (%a)" c (Pp.list ", " r) vs
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

let pp_method ppf name = function
  | None -> fprintf ppf "@\n@[method virtual eval_%s : %s -> 'a@]" name name
  | Some body -> 
      fprintf ppf "@\n@[<2>method eval_%s : %s -> 'a =@ %a@]" 
        name name pp_value body

let print ppf {modules=ms; evaluators=es} =
  fprintf ppf "@[";
  StringSet.iter (fun m -> fprintf ppf "open %s@\n" m) ms;
  fprintf ppf "@[<2>class virtual ['a] evaluator %s = object(self)" default;
  StringMap.iter (pp_method ppf) es;
  fprintf ppf "@\nmethod virtual combine : 'a -> 'a -> 'a@]@\nend@\n@]"
