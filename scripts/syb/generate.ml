(** code generator *)
(* open {{{ *)
open Ast
open Format
open Std
(* }}} *)
(* (optimizing) constructors {{{ *)
let v x = Code.V_var x

let mk_abs = function 
  | [] -> failwith "Code.V_abs must have a non-empty list"
  | [Code.P_var x, Code.V_app(f, Code.V_var y)] when x = y -> f
  | xs -> (* TODO: optimize when the pattern isn't used *)
      if List.for_all (fun (_, w) -> w = v"default_value") xs then
        Code.V_abs [Code.P_var "_", v"default_value"]
      else
        Code.V_abs xs

let mk_app fs v = 
  let rec substitute x v = function
    | Code.V_var y when x = y -> v
    | Code.V_var y as vy -> vy
    | Code.V_list vs -> Code.V_list (List.map (substitute x v) vs)
    | Code.V_tuple vs -> Code.V_tuple (List.map (substitute x v) vs)
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

let mk_map f = function
  | Code.V_list [] -> Code.V_list []
  | Code.V_list [v] -> Code.V_list [mk_app [f] v]
  | (Code.V_list _ as x)
  | (Code.V_app _ as x) 
  | (Code.V_var _ as x) -> mk_app [v"List.map"; f] x
  | _ -> failwith "you're trying to map over a non-list"

let mk_fun_type m n =
  let t_i = Ast.TE_id (Ast.Id m) in
  let t_o = Ast.TE_id (Ast.Id n) in
  Ast.TE_arrow (t_i, t_o)
(* }}} *)
(* (generic) visitor {{{ *)
class virtual visitor = object(self)
  (* "globals" {{{ *)
  val mutable modules = StringSet.empty
  val mutable methods = StringMap.empty
  val mutable mentioned_types = StringSet.empty
  val mutable last_var = 0
  (* }}} *)
  (* good defaults, probably not overriden {{{ *)
  method visit_ml_type {type_name=n; type_kind=k} =
    let m = {
      Code.mt_name = self#prefix () ^ n; 
      Code.mt_type = self#visit_type_name n;
      Code.mt_body = self#visit_type_kind k } in
    methods <- StringMap.add m.Code.mt_name m methods

  method constructor (c, t) =
    last_var <- 0;
    match self#visit_type_expr t with
      | Code.P_tuple ps, f -> self#wrap_constructor c ps, self#wrap_value c f
      | p, f -> Code.P_const (c, [p]), f

  method visit_type_kind = function
      TK_abstract -> Some (self#default_fun ())
    | TK_variant cs -> Some (mk_abs (List.map self#constructor cs))
    | TK_synonym t -> last_var <- 0; Some (mk_abs [self#visit_type_expr t])

  method visit_id =
    let v s = 
      mentioned_types <- StringSet.add s mentioned_types;
      Code.V_var (sprintf "self#%s%s" (self#prefix ()) s) in
    function
      | Id s -> v s
      | Dot (m, s) -> modules <- StringSet.add (id2str m) modules; v s
    
  method visit_ast ast =
    modules <- self#used_modules ();
    methods <- StringMap.empty;
    mentioned_types <- StringSet.empty;
    List.iter self#visit_ml_type ast;
    StringSet.iter (fun t -> 
      if not (StringMap.mem (self#prefix () ^ t) methods) then
      self#visit_ml_type {type_name=t; type_kind=TK_abstract})
      mentioned_types;
    {
      Code.md_opens = modules;
      Code.md_classes = StringMap.add
        (self#class_name ())
        {
          Code.c_name = self#class_name ();
          Code.c_type_vars = self#class_type_vars ();
          Code.c_arguments = self#class_arguments ();
          Code.c_methods = methods
        }
        StringMap.empty
    }
  (* }}} *)
  (* helpers, useful for subclasses too {{{ *)
  method fresh_var () =
    last_var <- succ last_var; sprintf "_%d" last_var

  method mk_open_abs fs =
    let x = self#fresh_var () in
    (Code.P_var x, mk_app fs (v x))
  (* }}} *)
  (* to be overriden {{{ *)
  method virtual class_name : unit -> string
  method virtual default_fun : unit -> Code.value
  method virtual prefix : unit -> string
  method virtual visit_type_expr : Ast.type_expr -> (Code.pattern * Code.value)
  method virtual visit_type_name : string -> Ast.type_expr
  method wrap_constructor c ps = Code.P_const (c, ps)
  method wrap_value _ v = v
  method used_modules () = StringSet.singleton "Jstar_std"
  method class_type_vars () = StringSet.empty
  method class_arguments () = []
  (* }}} *)
end
(* }}} *)
(* generating evaluators {{{ *)
class evaluator = object(self)
  inherit visitor

  method class_name () = "evaluator"
  method default_fun () = mk_abs [Code.P_var "_", v"default_value"]
  method prefix () = "eval_"
  method visit_type_name t = mk_fun_type t "'a"
  method class_type_vars () = StringSet.singleton "'a"
  method class_arguments () = ["default_value"]

  method mk_combine =
    methods <- StringMap.add "combine" {
      Code.mt_name = "combine";
      Code.mt_type = Ast.TE_arrow (Ast.TE_id (Ast.Id ("'a")), mk_fun_type "'a" "'a");
      Code.mt_body = None } methods;
    function
      | Code.V_list [] -> v"default_value"
      | Code.V_list [v] -> v
      | (Code.V_list _ as x)
      | (Code.V_app _ as x) -> 
          mk_app [v"List.fold_left"; v"self#combine"; v"default_value"] x
      | _ -> failwith "you're trying to combine a non-list"

  method visit_type_expr =
    let mk_abs_te x = mk_abs [self#visit_type_expr x] in
    function
      | TE_id t -> self#mk_open_abs [self#visit_id t]
      | TE_application ("option", t) -> 
          self#mk_open_abs [v"maybe"; v"default_value"; mk_abs_te t]
      | TE_application ("list", t) ->
          let x = self#fresh_var () in
          (Code.P_var x, self#mk_combine (mk_map (mk_abs_te t) (Code.V_var x)))
      | TE_tuple ts ->
          let f t = self#mk_open_abs [mk_abs_te t] in
          let ps, vs = List.split (List.map f ts) in
          (Code.P_tuple ps, self#mk_combine (Code.V_list vs))
      | _ -> failwith "todo: get rid of function types"
end
(* }}} *)
(* generating mappers {{{ *)
class mapper = object(self)
  inherit visitor

  method class_name () = "mapper"
  method default_fun () = v"identity"
  method prefix () = "map_"
  method visit_type_name t = mk_fun_type t t
  method wrap_value c = function
    | Code.V_tuple vs -> Code.V_const (c, vs)
    | _ -> failwith "Shouldn't this be a tuple?"

  method visit_type_expr =
    let mk_abs_te x = mk_abs [self#visit_type_expr x] in
    function
      | TE_id t -> 
          self#mk_open_abs [self#visit_id t]
      | TE_application ("option", t) -> 
          self#mk_open_abs [v"option_map"; mk_abs_te t]
      | TE_application ("list", t) ->
          self#mk_open_abs [v"List.map"; mk_abs_te t]
      | TE_tuple ts ->
          let f t = self#mk_open_abs [mk_abs_te t] in
          let ps, vs = List.split (List.map f ts) in
          (Code.P_tuple ps, Code.V_tuple vs)
      | _ -> failwith "todo: get rid of function types"
end
(* }}} *)
(* external interface {{{ *)
let evaluator = (new evaluator)#visit_ast
let mapper = (new mapper)#visit_ast

let empty_module : Code.modul_ = {
  Code.md_opens = StringSet.empty;
  Code.md_classes = StringMap.empty
}

let merge_modules m n = 
  StringMap.iter 
    (fun cn _ -> assert (not (StringMap.mem cn n.Code.md_classes)))
    m.Code.md_classes;
  { Code.md_opens = StringSet.union m.Code.md_opens n.Code.md_opens;
    Code.md_classes =
      let map_add = StringMap.fold StringMap.add in
      StringMap.empty |> map_add m.Code.md_classes |> map_add n.Code.md_classes}
(* }}} *)
