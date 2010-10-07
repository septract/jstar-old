(* Translation of Verified Featherweight C to jStar symbolic execution intermediate language *)

open VfcAST
open Vfclogic
open Core
open Spec
open Psyntax
open Spec_def


let fun_decls = Hashtbl.create 101
let struct_decls = Hashtbl.create 101
let fun_specs = Hashtbl.create 101
let invs = Hashtbl.create 101

let find hashtbl id =
  try Hashtbl.find hashtbl id
  with Not_found ->
    Printf.printf "Error: %s not found!\n" id;
    exit 1


(* Create fresh labels used in translation of conditionals and loops *)
let fresh_label =
  let label_ref = ref 0 in 
  fun () -> 
    label_ref := !label_ref + 1;
    Printf.sprintf "gen_%i" !label_ref

    
(* Create the variable for a parameter *)
let mk_parameter n =
  let parameter n = "@parameter"^(string_of_int n)^":" in
  let p = parameter n in 
  let v = prog_var p in
  v

  
let constant_to_term c =
  match c with 
(*  | Null_const -> mkFun "nil" [] *)
(*  | Int_const i -> mkFun "numeric_const" [mkString (Printf.sprintf "%d" i)] *)
  | Int_const i -> mkString (Printf.sprintf "%d" i)
  | Bool_const _ -> assert false


let term_term_ops = 
  [
    (Add, (fun args -> mkFun "builtin_plus" [List.nth args 0; List.nth args 1]));
    (Sub, (fun args -> mkFun "builtin_minus" [List.nth args 0; List.nth args 1]));
    (Neg, (fun args -> assert false)); (* TODO: handle neg *)
    (Mult, (fun args -> mkFun "builtin_mult" [List.nth args 0; List.nth args 1]))
  ]


let term_form_ops = 
  [
    (Cmpeq, (fun args -> mkEQ (List.nth args 0, List.nth args 1)));
    (Cmpne, (fun args -> mkNEQ (List.nth args 0, List.nth args 1)));
    (Cmpgt, (fun args -> mkPPred ("GT", [List.nth args 0; List.nth args 1])));
    (Cmplt, (fun args -> mkPPred ("LT", [List.nth args 0; List.nth args 1])));
    (Cmpge, (fun args -> mkPPred ("GE", [List.nth args 0; List.nth args 1])));
    (Cmple, (fun args -> mkPPred ("LE", [List.nth args 0; List.nth args 1])))
  ]


let form_form_ops = 
  [
    (And, (fun args -> mkStar (List.nth args 0) (List.nth args 1)));
    (Or, (fun args -> mkOr (List.nth args 0, List.nth args 1)))
  ]


let rec negate_expr (e : pexp) : pexp =
  match e with
  | Prim_op (op_name, args) ->
    begin
    match op_name with
      | Cmpeq -> Prim_op (Cmpne, args)
      | Cmpne -> Prim_op (Cmpeq, args)
      | Cmpgt -> Prim_op (Cmple, args)
      | Cmplt -> Prim_op (Cmpge, args)
      | Cmpge -> Prim_op (Cmplt, args)
      | Cmple -> Prim_op (Cmpgt, args)
      | And -> Prim_op (Or, List.map negate_expr args)
      | Or -> Prim_op (And, List.map negate_expr args)
      | _ -> e
    end
  | _ -> e


(* Translation of expression to term *)
let rec tr_expr2term (e : pexp) : term =
  match e with
  | Const c -> 
    constant_to_term c
  | PVar_ref v_id ->
    begin
      match v_id with
      | "local" | "host" -> mkString v_id (* TODO: sort this out more elegantly *)
      | _ -> mkVar (prog_var v_id)
    end
  | Prim_op (op_name, args) ->
    let op = 
      try List.assoc op_name term_term_ops
      with Not_found -> assert false (* TODO: lift bool expr to int *)
    in op (List.map tr_expr2term args)


(* Translation of expression to form *)
let rec tr_expr2form (e : pexp) : form =      
  match e with
  | Const (Bool_const b) ->
    begin
      match b with
      | true -> mkEmpty
      | false -> mkFalse
    end
  | Prim_op (op_name, args) ->
    if List.mem_assoc op_name form_form_ops then
      let op = List.assoc op_name form_form_ops in
      op (List.map tr_expr2form args)
    else if List.mem_assoc op_name term_form_ops then
      let op = List.assoc op_name term_form_ops in
      op (List.map tr_expr2term args)
    else
      assert false (* TODO: lift int expr to bool *)
  | _ ->  assert false


let retvar = Spec.ret_v1
let retvar_term = mkVar retvar

let parameter_var n = prog_var (Support_syntax.parameter n)

let excep_post_empty = ClassMap.empty

let invariants_empty = LabelMap.empty

(* Assume in core language *)
let assume_core (e : form) =
  Assignment_core([], mk_spec [] e excep_post_empty invariants_empty, []) 


(* Translation of statement *)
let rec tr_stmt (s : stmt) : core_statement list =
  match s with 
  | PVar_decl v -> [] (* TODO: Add type info *)
  
  | Assign (v_id, e) ->
    let post = mkEQ (retvar_term, tr_expr2term e) in
    let spec = mk_spec [] post excep_post_empty invariants_empty in
    [Assignment_core ([prog_var v_id], spec, [])]

  | Cast (v_id, t, e) -> [] (* TODO: Handle cast properly *)
  
  | Heap_read (v_id, e, fo) ->
    let typ = mk_type Byte in (* TODO: sort out handling of types; everything byte for now *)
    let e_var = fresh_exists_var() in
    let pointed_to_var = mkVar e_var in
    let x = tr_expr2term e in 
    let pre = mk_local_blob typ (mk_loc x fo) pointed_to_var in
    let post = mkStar (mkEQ (retvar_term, pointed_to_var)) (mk_local_blob typ (mk_loc x fo) pointed_to_var) in
    let spec = mk_spec pre post excep_post_empty invariants_empty in
    [Assignment_core ([prog_var v_id], spec, [])]
  
  | Heap_assn (e, fo, e') ->
    let typ = mk_type Byte in (* TODO: sort out handling of types; everything byte for now *)
    let e_var = fresh_exists_var() in
    let pointed_to_var = mkVar e_var in
    let p0 = tr_expr2term e in (* TODO: should be a fresh program variable? *)
    let p1 = tr_expr2term e' in
    let pre = mk_local_blob typ (mk_loc p0 fo) pointed_to_var in
    let post = mk_local_blob typ (mk_loc p0 fo) p1 in
    let spec = mk_spec pre post excep_post_empty invariants_empty in
    [Assignment_core ([], spec, [])]
  
  | Skip -> []

  | Block stmts ->
    List.concat (List.map tr_stmt stmts)

  | If (e, s1, s2) -> 
    let l1 = fresh_label() in 
    let l2 = fresh_label() in 
    [Goto_stmt_core ([l1; l2]); Label_stmt_core l1; assume_core (tr_expr2form e)] @
    (tr_stmt s1) @
    [Label_stmt_core l2; assume_core (tr_expr2form (negate_expr e))] @
    (tr_stmt s2)
  (*| While of pexp * lexp option * stmt*)
 
 | While (e, i, s) ->
    let inv_stmt_core =
      match i with
      | Some inv_id ->
        let inv = find invs inv_id in
        let spec = mk_spec inv inv excep_post_empty invariants_empty in
        [Assignment_core ([], spec, [])]
      | None -> []
    in
    let l_loop_top = fresh_label() in
    let l_loop_body = fresh_label() in
    let l_loop_exit = fresh_label() in
    inv_stmt_core @
    [Label_stmt_core l_loop_top; Goto_stmt_core ([l_loop_body; l_loop_exit]);
    Label_stmt_core l_loop_body; assume_core (tr_expr2form e)] @
    (tr_stmt s) @
    inv_stmt_core @
    [Goto_stmt_core ([l_loop_top]); 
    Label_stmt_core l_loop_exit; assume_core (tr_expr2form (negate_expr e))]

  | Return e ->
    begin
      match e with
      | Some e' ->
        let p0 = Arg_var (mk_parameter 0) in (* TODO: should be a fresh program variable? *)
        let post = mkEQ (retvar_term, p0) in
        let spec = mk_spec [] post excep_post_empty invariants_empty in
        [Assignment_core ([], spec, [tr_expr2term e']); End]
      | None -> [Nop_stmt_core]
    end

  | Fun_call (vo, fun_id, args) ->
    let (pre, post) = find fun_specs fun_id in
    let params =
      match fun_id with (* TODO: sort this out using function prototypes; need a support for header files for that *)
      | "free" | "wait"  -> [ { vname="@parameter0:"; vtype=Byte; kind=Parameter; }  ]
      | "alloc" -> [ { vname="@parameter0:"; vtype=Byte; kind=Parameter; }; { vname="@parameter1:"; vtype=Byte; kind=Parameter; } ]
      | "memcpy" ->  [ { vname="@parameter0:"; vtype=Byte; kind=Parameter; }; { vname="@parameter1:"; vtype=Byte; kind=Parameter; }; { vname="@parameter2:"; vtype=Byte; kind=Parameter; } ]
      | "get" | "put" -> [ { vname="@parameter0:"; vtype=Byte; kind=Parameter; }; { vname="@parameter1:"; vtype=Byte; kind=Parameter; }; { vname="@parameter2:"; vtype=Byte; kind=Parameter; }; { vname="@parameter3:"; vtype=Byte; kind=Parameter; } ]
      | _ -> (find fun_decls fun_id).params
    in
    let pvars = List.fold_right (fun v -> vs_add (prog_var v.vname)) params 
      (vs_add retvar vs_empty) in
    let lvars = vs_diff (fv_form pre) pvars in
    let psubst = ref empty_subst in
(*
    List.iter (fun (v, e) ->
      psubst := add_subst (prog_var v.vname) (tr_expr2term e) !psubst
    ) (List.combine params args);
*)
    let cnt = ref 0 in
    List.iter (fun v ->
      psubst := add_subst (prog_var v.vname) (mkVar (parameter_var !cnt)) !psubst;
      cnt := !cnt + 1;
    ) params;
    psubst := add_subst retvar retvar_term !psubst; 
    (* make logical variables fresh to avoid capture *)
    let lsubst = subst_kill_vars_to_fresh_exist lvars in
    let pre = subst_form lsubst (subst_form !psubst pre) in
    (* substitution makes existentials in post that aren't already handled into prog variables *)
    let evars = vs_diff (vs_diff (fv_form post) pvars) lvars in
    let esubst = subst_kill_vars_to_fresh_prog evars in
    let post = subst_form esubst (subst_form lsubst (subst_form !psubst post)) in
    let spec = mk_spec pre post excep_post_empty invariants_empty in
    let tr_args = List.map tr_expr2term args in
(*    [Assignment_core ([prog_var v_id], spec, [])]*)
    begin
      match vo with
      | Some v_id -> [Assignment_core ([prog_var v_id], spec, tr_args)]
      | None -> [Assignment_core ([], spec, tr_args)]
    end

  (* TODO *)
  | Fork (v_id, fun_id, e) -> []
  | Join t -> []

  | Inv inv_id ->
    let inv = find invs inv_id in
    let spec = mk_spec inv inv excep_post_empty invariants_empty in
    [Assignment_core ([], spec, [])]
  
  | Abstract ->
    let l = fresh_label() in 
    [Label_stmt_core l]

(*
  | Alloc (v_id, e) -> []
  | Free e -> []
  | Get (l, h, s, t) -> []
  | Put (l, h, s, t) -> []
  | Wait t -> []
*)  


(* Verifies functions in prog against specs using given logic and abstraction rules *)
let verify
    (file_prefix : string)
    (prog : vfc_prog)
    (specs : vfc_spec list)
    (lo : logic) 
    (abs_rules : logic) : unit =

  List.iter (fun decl ->
    match decl with
    | Fun_decl f -> 
      Hashtbl.add fun_decls f.fun_name f;  (* Note: function names must be unique *)    
    | Struct_decl s ->
      Hashtbl.add struct_decls s.sname s;
      (* TODO: add struct rules to logic *)
      (* updateLogic ((fun l -> Logic.add_struct_to_rules t l)) *)
  ) prog;  

  List.iter (fun spec ->
    match spec with
    | Vfc_inv (inv_id, inv) ->
      Hashtbl.add invs inv_id inv;
    | Vfc_fun (fun_id, pre, post) ->
      Hashtbl.add fun_specs fun_id (pre, post);
  ) specs;

  Symexec.file := file_prefix;
  (* TODO: generate call graph, and perform the fixpoint abduction *)
  (* for now: verification of each method separately against a given spec *)
  List.iter (fun decl ->
    match decl with
    | Fun_decl f ->
      let fun_name_str = f.fun_name in
      if Config.symb_debug() then Printf.printf "Starting verification of function %s...\n" fun_name_str;
      (* add function parameters *)
      let params_stmts =
        let cnt = ref 0 in
        List.map (fun v ->
          let post = mkEQ (mkVar (parameter_var !cnt), mkVar (prog_var v.vname)) in
          cnt := !cnt + 1;
          let spec = mk_spec [] post excep_post_empty invariants_empty in
          Assignment_core ([], spec, [])
        ) f.params in
      (* add function body *)
      let body_stmts = tr_stmt f.body in
      let core_stmts = params_stmts @ body_stmts in
      let cfg_nodes = List.map (fun s -> Cfg_core.mk_node s) core_stmts in
      Cfg_core.print_core (file_prefix ^ ".") fun_name_str cfg_nodes;
      let (pre, post) = find fun_specs fun_name_str in
      let spec = mk_spec pre post excep_post_empty invariants_empty in
      let res = Symexec.verify fun_name_str cfg_nodes spec lo abs_rules in
      if res then
        Printf.printf "Verification of %s succeeded.\n" fun_name_str
      else
        Printf.printf "Verification of %s failed!\n" fun_name_str
    | _ -> ()
  ) prog 
