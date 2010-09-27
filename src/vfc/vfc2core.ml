(* Translation of Verified Featherweight C to jStar symbolic execution intermediate language *)

open VfcAST
open Vfclogic
open Core
open Cfg_core
open Spec
open Psyntax


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
  | Int_const i -> mkFun "numeric_const" [mkString (Printf.sprintf "%d" i)]
(*  | Bool_const -> assert false *)


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
    mkVar (prog_var v_id)
  | Prim_op (op_name, args) ->
    let op = 
      try List.assoc op_name term_term_ops
      with Not_found -> assert false (* TODO: lift bool expr to int *)
    in op (List.map tr_expr2term args)


(* Translation of expression to form *)
let rec tr_expr2form (e : pexp) : form =      
  match e with
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


let retvar_term = mkVar (Spec.ret_v1)

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
  
  | Field_read (v_id, e, f_id) ->
    let e_var = fresh_exists_var() in
    let pointed_to_var = mkVar e_var in
    let x = tr_expr2term e in 
    let pre = mk_pointsto x (mkString f_id) pointed_to_var in
    let post = mkStar (mkEQ (retvar_term, pointed_to_var)) (mk_pointsto x (mkString f_id) pointed_to_var) in
    let spec = mk_spec pre post excep_post_empty invariants_empty in
    [Assignment_core ([prog_var v_id], spec, [])]
  
  | Field_assn (e, f_id, e') -> 
    let e_var = fresh_exists_var() in
    let pointed_to_var = mkVar e_var in
    let p0 = tr_expr2term e in (* TODO: should be a fresh program variable? *)
    let p1 = tr_expr2term e' in
    let pre = mk_pointsto p0 (mkString f_id) pointed_to_var in
    let post = mk_pointsto p0 (mkString f_id) p1 in
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
 
 | While (e, s) ->
    let l_loop_top = fresh_label() in 
    let l_loop_body = fresh_label() in  
    let l_loop_exit = fresh_label() in  
    [Label_stmt_core l_loop_top; Goto_stmt_core ([l_loop_body; l_loop_exit]);
    Label_stmt_core l_loop_body; assume_core (tr_expr2form e)] @
    (tr_stmt s) @
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

  | Fun_call (v_id, fun_id, e) -> [] (* TODO: use contracts on function call *)
  
  | Alloc (v_id, e) -> []
  | Free e -> []
  | Fork (v_id, fun_id, e) -> []
  | Join t -> []
  | Get (l, h, s, t) -> []
  | Put (l, h, s, t) -> []
  | Wait t -> [] (* TODO: treat via function call *)
  | Inv i_id -> [] (* TODO *)


let function_signature_str f =
  f.fun_name
  

let verify (spec : Spec.spec) (* temporary *)
    (prog : vfc_prog)
    (lo : logic) 
    (abs_rules : logic) : unit =

  (* TODO: add struct rules to logic *)
  List.iter (fun decl ->
    match decl with
    | Struct_decl s -> () (* updateLogic ((fun l -> Logic.add_struct_to_rules t l)) *)
    | _ -> ()
  ) prog;  
  
  (* TODO: generate call graph, and perform the fixpoint abduction *)
  (* for now: verification of each method separately against a given spec *)
  let file = ref "" in
  List.iter (fun decl ->
    match decl with
    | Fun_decl f ->
      let fun_name_str = function_signature_str f in
      let core_stmts = tr_stmt f.body in
      let cfg_nodes = List.map (fun s -> mk_node s) core_stmts in
      print_core !file fun_name_str cfg_nodes;
      let res = Symexec.verify fun_name_str cfg_nodes spec lo abs_rules in
      if res then
        Printf.printf "Verification of %s succeeded." (f.fun_name)
      else
        Printf.printf "Verification of %s failed!" (f.fun_name)
    | _ -> ()
  ) prog 
