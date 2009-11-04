(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Pterm
open Plogic
open Rlogic
open Jlogic
open Jimple_global_types
open Jparsetree
open Spec_def
open Prover
open Specification
open Vars
open Support_symex
open Symexec

(* global variables *)
let curr_static_methodSpecs:Specification.methodSpecs ref = ref Specification.emptyMSpecs
let curr_dynamic_methodSpecs:Specification.methodSpecs ref = ref Specification.emptyMSpecs




(* create local program variables for methods. 
   mdl is the list of all methods in the class file.
   A special return variable (called method_name$ret) is created as well.
 *)
let create_program_variables mdl =
  let process_method md =
    let lv=snd (List.split md.locals) in
    let lv = List.map (fun v -> Var_name v) lv in
    let lv = Var_name(Identifier_name(name_ret_var))::lv in
    let locs= List.map (fun v -> variable2key v, Vars.concretep_str (variable2key v)) lv in
    List.iter (fun (k,v) -> var_table_add k v) locs
  in 
  List.iter process_method mdl





(* ================  transition system ==================  *)
(*
type id = int

let set_group,grouped = let x = ref false in (fun y -> x := y),(fun () -> !x )

let fresh_node = let node_counter = ref 0 in fun () ->  let x = !node_counter in node_counter := x+1; x

let fresh_file = let file_id = ref 0 in fun () -> let x = !file_id in file_id := x+1;  Sys.getcwd() ^  "/" ^ !file ^ ".proof_file_"^(string_of_int x)^".txt"

type node = {mutable content : string; id : id; mutable ntype : ntype; mutable url : string; mutable edges : edge list; cfg : Cfg.node_jimple option}
and  edge = string * string * node * node * string option

let graphe = ref []

let mk_node c id nt url ed cfg =
 { content =c; 
   id =id; 
   ntype =nt; 
   url =url; 
   edges =ed; 
   cfg =cfg
 }




module Idmap = 
  Map.Make(struct 
	     type t = int option 
	     let compare = compare
	   end)

let graphn = ref  Idmap.empty
let startnodes: node list ref = ref []

let make_start_node node = startnodes := node::!startnodes

let escape_for_dot_label s =
  Str.global_replace (Str.regexp "\\\\n") "\\l" (String.escaped s)

let pp_dotty_transition_system () =
  let foname = (!file) ^ ".execution_core.dot~" in
  let dotty_outf=open_out foname in
  if Config.symb_debug() then Printf.printf "\n Writing transition system file execution_core.dot  \n";
  Printf.fprintf dotty_outf "digraph main { \nnode [shape=box,  labeljust=l];\n\n";
  Idmap.iter 
    (fun cfg nodes ->
      ((
       if grouped () then match cfg with Some cfg -> Printf.fprintf dotty_outf "subgraph cluster_cfg%i {\n"  cfg | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=escape_for_dot_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	  Plain -> ()
	| Good ->  ()
	| Error ->  ()
	| UnExplored -> ()
	| Abs ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=yellow, style=filled%s]\n" id label url)
	nodes;
      if grouped () then match cfg with Some _ -> Printf.fprintf dotty_outf "\n}\n" | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=escape_for_dot_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	  Plain ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l%s]\n" id label url
	| Good ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=green, style=filled%s]\n" id label url
	| Error ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=red, style=filled%s]\n" id label url
	| UnExplored ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=orange, style=filled%s]\n" id label url
	| Abs -> () )
	nodes;
    )
    !graphn;
  List.iter (fun (l,c,s,d, o) ->
    let l = escape_for_dot_label l in
    let c = escape_for_dot_label c in
    Printf.fprintf dotty_outf "\n state%i -> state%i [label=\"%s\", tooltip=\"%s\"%s]" s.id d.id l c
	    (match o with 
	      None -> ""
	    | Some f -> Printf.sprintf ", URL=\"file://%s\", fontcolor=blue" f))
    !graphe;
  Printf.fprintf dotty_outf "\n\n\n}";
  close_out dotty_outf;
  Sys.rename foname (!file ^ ".execution_core.dot")


let add_node (label : string) (ty : ntype) (cfg : Cfg.node_jimple option) = 
  let id = fresh_node () in 
  let node = {content=label; id=id;ntype=ty;url=""; edges=[]; cfg = cfg} in 
  let cfgid = 
    match cfg with 
      None -> None 
    | Some cfg -> Some (node_get_id cfg) in 
  graphn := Idmap.add cfgid (node::(try Idmap.find cfgid !graphn with Not_found -> [])) !graphn;
  node

let add_error_node label = add_node label Error None
let add_abs_node label cfg = add_node label Abs (Some cfg)
let add_good_node label = add_node label Good None
let add_node_unexplored label cfg = add_node label UnExplored (Some cfg)
let add_node label cfg = add_node label UnExplored (Some cfg)

let explore_node src = if src.ntype = UnExplored then src.ntype <- Plain

let add_abs_heap_node (heap : Rlogic.ts_form) cfg= 
  (Format.fprintf (Format.str_formatter) "%a" string_ts_form heap);
  add_abs_node (Format.flush_str_formatter ()) cfg

let add_heap_node (heap : Rlogic.ts_form) cfg = 
  (Format.fprintf (Format.str_formatter) "%a" string_ts_form heap);
  add_node (Format.flush_str_formatter ()) cfg

let add_error_heap_node (heap : Rlogic.ts_form) = 
  (Format.fprintf (Format.str_formatter) "%a" string_ts_form heap);
  add_error_node (Format.flush_str_formatter ())

let x = ref 0


let add_edge src dest label = 
  let edge = (label, "", src, dest, None) in
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  explore_node src;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1


let add_edge_with_proof src dest label = 
  let f = fresh_file() in
  let out = open_out f in
  Prover.pprint_proof out;
  close_out out;
  explore_node src;
  let edge = (label, "", src, dest, Some f) in 
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1

(*let add_edge_with_string_proof src dest label proof = 
  let f = fresh_file() in
  let out = open_out f in
  output_string out proof;
  close_out out;
  graphe := (label, src, dest, Some f)::!graphe*)

let add_url_to_node src proof = 
  let f = fresh_file() in
  let out = open_out f in
  List.iter (output_string out) proof;
  close_out out;
  src.url <- f

let add_id_form h cfg =
    let id=add_heap_node h cfg in
    (h,id)

let add_id_formset sheaps cfg =  List.map (fun h -> add_id_form h cfg) sheaps

let add_id_abs_form cfg h =
    let id=add_abs_heap_node h cfg in
    (h,id)

let add_id_abs_formset sheaps cfg =  List.map (add_id_abs_form cfg) sheaps
*)

(* ================   ==================  *)



(* ================ Transliation from Jimple statements to core statements  ==================  *)

(* create entries in the variable table for a  parameter *)
let mk_parameter n =
  let p=parameter n in 
  let v=Vars.concretep_str p
  in var_table_add p v;
  v
  

(* retrieve static spec of a method from table of specs*)
let get_static_spec si = 
  match si with 
  | Method_signature ms ->
      (try 
	Some (MethodMap.find ms !curr_static_methodSpecs  )
      with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false

(* retrieve dynamic spec of a method from table of specs*)
let get_dynamic_spec si = 
  match si with 
  | Method_signature ms ->
      (try 
	 Some (MethodMap.find ms !curr_dynamic_methodSpecs  )
       with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false



let get_spec  (iexp: Jparsetree.invoke_expr) = 
  match iexp with
  | Invoke_nostatic_exp (Virtual_invoke,n,si,il) 
  | Invoke_nostatic_exp (Interface_invoke,n,si,il) ->  (* ddino: we deal with interface invoke as for virtual invoke. Not sure it's correct!!!*)
      (match get_dynamic_spec si with
       | Some dspec -> 
	   let il = match il with 
	     None -> []
	   | Some il -> il in
	   let subst = Pterm.empty in 
	   let subst = Pterm.add (mk_this_of_class ()) (Arg_var (mk_parameter (List.length il))) subst in 
	   sub_spec subst dspec,Some (il@[Immediate_local_name(n)])
       | _ -> 
	   warning(); Printf.printf "\n No dynamic specs found for %s. Abort!\n\n" (Pprinter.signature2str si); reset();
	   assert false	  
      )
  | Invoke_nostatic_exp (Special_invoke,n,si,il) ->
      (match get_static_spec si with
      | Some sspec -> sspec,il
      |  _ ->	
	   warning(); Printf.printf "\n No static specs found for %s. Abort!\n\n" (Pprinter.signature2str si); reset();
	   assert false	  
      )
  | Invoke_static_exp (si,il) -> 
      (match get_static_spec si with
      | Some sspec -> sspec,il
      |  _ ->	
	   warning(); Printf.printf "\n No static specs found for %s. Abort!\n\n" (Pprinter.signature2str si); reset();
	   assert false	  
      )




let rec translate_assign_stmt  (v:Jparsetree.variable) (e:Jparsetree.expression) =
  match v, e with 
  | Var_ref (Field_local_ref (n,si)), Immediate_exp e'  -> 
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      (* execute  n.si=e' --> _:={param0.si|->-}{param0.si|->param1 * return=x'}(n,e') *)
      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let p1 = Arg_var(mk_parameter 1) in
      let pre=mk_pointsto p0 (signature2args si) pointed_to_var in
      let post=mk_pointsto p0 (signature2args si) p1 in
      let spec=Spec_def.mk_spec pre post Spec_def.ClassMap.empty in
      Global_types.Assignment_core ([],spec,Some [Immediate_local_name(n);e'])	
  | Var_name n, Immediate_exp e' -> 
      (* execute  v=e' --> v:={emp}{return=param0}(e') *)
      let retvar = Arg_var(variable2var  (Var_name(Identifier_name(name_ret_var)))) in
      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let post= mkEQ(retvar,p0) in
      let spec=Spec_def.mk_spec [] post Spec_def.ClassMap.empty in
      Global_types.Assignment_core  ([Var_name(n)],spec,Some [e'])

  | Var_name v, Reference_exp (Field_local_ref (n,si))  -> 
      (* execute v=n.si --> v:={param0.si|->z}{param0.si|->z * return=z}(n)*)
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      let retvar = Arg_var(variable2var  (Var_name(Identifier_name(name_ret_var)))) in
      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let pre=mk_pointsto p0 (signature2args si) pointed_to_var in
      let post=pconjunction (mkEQ(retvar,pointed_to_var)) (mk_pointsto p0 (signature2args si) pointed_to_var) in
      let spec=Spec_def.mk_spec pre post Spec_def.ClassMap.empty in
      Global_types.Assignment_core ([Var_name v],spec,Some [Immediate_local_name(n)])	
  | Var_name n, New_simple_exp ty ->
      (* execute x=new(ty) --> x:=null 
	 We treat it as just assigning null to x. This should have the effect
	 to substitute the occurrences of x with a fresh variable. 
	 The rest of the job will be performed by the invocation to specialinvoke <init>
      *)
      translate_assign_stmt (Var_name(n)) (Immediate_exp(Immediate_constant(Null_const)))	
  | Var_name n , Binop_exp(name,x,y)-> 
      let retvar = Arg_var(variable2var  (Var_name(Identifier_name(name_ret_var)))) in
      let p0 = Arg_var(mk_parameter 0) in 
      let p1 = Arg_var(mk_parameter 1) in 
      let args = Arg_op(Support_syntax.bop_to_prover_arg name, [p0;p1]) in
      let post= mkEQ(retvar,args) in
      let spec=Spec_def.mk_spec [] post Spec_def.ClassMap.empty in
      Global_types.Assignment_core  ([Var_name(n)],spec,Some [x;y])
  | Var_name n , Cast_exp (_,e') -> (* TODO : needs something for the cast *) 
      translate_assign_stmt (Var_name n) (Immediate_exp(e'))
  | Var_name n , Invoke_exp ie ->  
      let spec,param=get_spec ie in
      Global_types.Assignment_core ([Var_name n],spec,param)	      
  | _ , _ -> assert false 


let jimple_statement2core_statement s =
  match s with 
  | Label_stmt l -> Global_types.Label_stmt_core l
  | Breakpoint_stmt -> assert false
  | Entermonitor_stmt i -> assert false
  | Exitmonitor_stmt i -> assert false
  | Tableswitch_stmt (i,cl) -> assert false
  | Lookupswitch_stmt(i,cl) -> assert false
  | Identity_stmt(nn,id,ty) -> 
      (* nn := id: LinkedLisr   ---> nn:={emp}{return=param0}(id)*)
      if Config.symb_debug() then 
	Printf.printf "\n Translating a jimple identity statement \n  %s\n" (Pprinter.statement2str s);
      let retvar = Arg_var(variable2var  (Var_name(Identifier_name(name_ret_var)))) in
      let id'=Immediate_local_name(Identifier_name(id)) in 
      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let post= mkEQ(retvar,p0) in
      let spec=Spec_def.mk_spec [] post Spec_def.ClassMap.empty in
      Global_types.Assignment_core  ([Var_name(nn)],spec,Some [id']) 
  | Identity_no_type_stmt(n,i) -> assert false
  | Assign_stmt(v,e) -> 
      if Config.symb_debug() then 
	Printf.printf "\n Translating a jimple assignment statement  %s\n" (Pprinter.statement2str s);
      translate_assign_stmt v e
  | If_stmt(b,l) ->
      if Config.symb_debug() then Printf.printf "\n Translating a jimple conditional jump statement  %s\n" (Pprinter.statement2str s);  
      Global_types.If_stmt_core(b,l) 
  | Goto_stmt(l) ->
      if Config.symb_debug() then Printf.printf "\n Translating a jimple goto statement  %s\n" (Pprinter.statement2str s);    
      Global_types.Goto_stmt_core(l)
  | Nop_stmt ->  
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Nop statement  %s\n" (Pprinter.statement2str s);    
      Global_types.Nop_stmt_core
  | Ret_stmt(i)  (* return i ---->  ret_var:=i  or as nop operation if it does not return anything*)
  | Return_stmt(i) -> 
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Return statement  %s\n" (Pprinter.statement2str s);    
      (match i with 
       | None -> Global_types.Nop_stmt_core 
       | Some e' -> let retvar = Arg_var(variable2var  (Var_name(Identifier_name(name_ret_var)))) in
	 let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
	 let post= mkEQ(retvar,p0) in
	 let spec=Spec_def.mk_spec [] post Spec_def.ClassMap.empty in
	 Global_types.Assignment_core  ([],spec,Some [e']) 
      )
  | Throw_stmt(i) ->
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Throw statement %s\n" (Pprinter.statement2str s);      
      Global_types.Throw_stmt_core(i)
  | Invoke_stmt (e) -> 
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Invoke statement %s \n" (Pprinter.statement2str s);      
      let spec,param=get_spec e in
      Global_types.Assignment_core ([],spec,param)	      

(* ================   ==================  *)









let get_class_name_from_signature si =
  match si with
  | Method_signature (c,_,_,_) -> c
  | Field_signature (c,_,_) ->c



exception Contained

(* 
recognise if md describes a init method. At the moment it only uses the name. But
maybe we should use a stronger condition
*)
let is_init_method md = Pprinter.name2str md.name_m ="<init>"



let methdec2signature_str dec =
  Pprinter.class_name2str dec.class_name ^ "." ^ Pprinter.name2str dec.name_m ^ "(" ^ (Pprinter.list2str Pprinter.parameter2str  dec.params ", ") ^ ")"


(* takes a jimple_methedec and transtalet it in a core methdec *)
let jimple_methdec2core_methdec
    (m_jimple: Jimple_global_types.methdec_jimple) : Global_types.methdec  = 
  let do_one_stmt stmt_jimple =
    let s=jimple_statement2core_statement stmt_jimple.skind in
    if Config.symb_debug() then Printf.printf "\n into the core statement: \n   %s \n" (Pprinter_core.statement_core2str s); 
    Methdec_core.stmt_create s [] [] 
  in
  let stmt_core_list =List.map do_one_stmt m_jimple.bstmts in
  Global_types.mk_methdec  m_jimple.modifiers m_jimple.class_name m_jimple.ret_type m_jimple.name_m m_jimple.params m_jimple.locals m_jimple.th_clause stmt_core_list 

let jimple_methdec2core_body
    (m_jimple: Jimple_global_types.methdec_jimple) = 
  let do_one_stmt stmt_jimple =
    let s=jimple_statement2core_statement stmt_jimple.skind in
    if Config.symb_debug() then Printf.printf "\n into the core statement: \n   %s \n" (Pprinter_core.statement_core2str s); 
    Methdec_core.stmt_create s [] [] 
  in
  List.map do_one_stmt m_jimple.bstmts



(* returns a triple (m,initial_formset, final_formset)*)
let get_spec_for m fields cname= 
  let this =mk_this_of_class () in
  let rec make_this_fields fl=
    match fl with
    |[] -> []
    | Field(mol,ty,n)::fl' -> 
	let e = Support_symex.default_for ty n in 
	let si=make_field_signature cname ty n in
	pconjunction (mk_pointsto (var2args this) (signature2args si) e) (make_this_fields fl')
    | _ -> assert false
  in
  let class_this_fields=make_this_fields fields in

  let msi = Methdec.get_msig m cname in
  let _=mk_parameter_of_class m.params in
  let spec=
    try 
      MethodMap.find msi !curr_static_methodSpecs 
    with  Not_found -> 
      warning(); Format.printf "\n\n Error: Cannot find spec for method %s\n\n" (methdec2signature_str m); reset();
      assert false
  in
  let spec = logical_vars_to_prog spec in 
  if is_init_method m then (* we treat <init> in a special way*)
    {pre=pconjunction spec.pre class_this_fields; post=spec.post; excep=spec.excep }
  else spec




(* implements a work-list fidex point algorithm *)
(* the queue qu is a list of pairs [(node, expression option)...] the expression
is used to deal with if statement. It is the expression of the if statement is the predecessor
of the node is a if_stmt otherwise is None. In the beginning is always None for each node *)
let compute_fixed_point 
    (f : Jimple_global_types.jimple_file) 
    (apfmap : logic Spec_def.ClassMap.t) 
    (lo : logic) 
    (abs_rules : logic)
    (sspecs: Specification.methodSpecs) 
    (dspecs: Specification.methodSpecs)  =

  
  curr_static_methodSpecs:=sspecs;
  curr_dynamic_methodSpecs:=dspecs;
  let cname=Methdec.get_class_name f in
  let lo = try let x=Spec_def.ClassMap.find cname apfmap in x with Not_found -> lo in
  let mdl =  Methdec.make_methdecs_of_list cname (Methdec.get_list_methods f) in
  let mdl = List.filter (fun y -> List.for_all (fun x-> Abstract<>x) (y.modifiers)) mdl in
  let fields=Methdec.get_list_fields f in
  create_program_variables mdl;  
  List.iter 
    (fun m ->
      let spec = get_spec_for m fields cname in
      let body = jimple_methdec2core_body m in 
      Symexec.compute_fixed_point body spec lo abs_rules
      ) mdl

