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
open Methdec_core
open Javaspecs

(* global variables *)
let curr_static_methodSpecs: Javaspecs.methodSpecs ref = ref Javaspecs.emptyMSpecs
let curr_dynamic_methodSpecs: Javaspecs.methodSpecs ref = ref Javaspecs.emptyMSpecs


let fresh_label =
  let label_ref = ref 0 in 
  fun () -> 
    label_ref := !label_ref + 1;
    Printf.sprintf "gen_%i" !label_ref




(* create the variable for a  parameter *)
let mk_parameter n =
  let p=parameter n in 
  let v=Vars.concretep_str p in
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
  let spec = 
    match iexp with 
    | Invoke_nostatic_exp (Virtual_invoke,_,si,_) 
    | Invoke_nostatic_exp (Interface_invoke,_,si,_) ->  
	(match get_dynamic_spec si with
	  Some spec -> spec
	| None -> 
	    System.warning(); Printf.printf "\n No dynamic specs found for %s. Abort!\n\n" (Pprinter.signature2str si); System.reset();
	    assert false	  )
    | Invoke_nostatic_exp (Special_invoke,_,si,_) 
    | Invoke_static_exp (si,_) -> 
	(match get_static_spec si with 
	  Some spec -> spec
	| None -> 	   
	    System.warning(); Printf.printf "\n No static specs found for %s. Abort!\n\n" (Pprinter.signature2str si); System.reset();
	    assert false	  )
  in
  match iexp with
  | Invoke_nostatic_exp (Virtual_invoke,n,_,il) 
  | Invoke_nostatic_exp (Interface_invoke,n,_,il) 
  | Invoke_nostatic_exp (Special_invoke,n,_,il) ->
      (* Make "this" be the final parameter, i.e. subst @this: for @parametern: *) 
      let subst = Pterm.add (mk_this) (Arg_var (mk_parameter (List.length il))) Pterm.empty in 
      sub_spec subst spec,(il@[Immediate_local_name(n)])
  | Invoke_static_exp (si,il) -> 
      spec,il
      



	
let retvar_term = Arg_var(ret_var) 

let rec translate_assign_stmt  (v:Jparsetree.variable) (e:Jparsetree.expression) =
  match v, e with 
  | Var_ref (Field_local_ref (n,si)), Immediate_exp e'  -> 
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      (* execute  n.si=e' --> _:={param0.si|->-}{param0.si|->param1 * return=x'}(n,e') *)
      let p0 = immediate2args (Immediate_local_name(n)) in (* ddino: should it be a fresh program variable? *)
      let p1 = immediate2args e' in
      let pre=mk_pointsto p0 (signature2args si) pointed_to_var in
      let post=mk_pointsto p0 (signature2args si) p1 in
      let spec=Specification.mk_spec pre post Specification.ClassMap.empty in
      Assignment_core ([],spec,[])	
  | Var_name n, Immediate_exp e' -> 
      (* execute  v=e' --> v:={emp}{return=param0}(e') *)
      let post= mkEQ(retvar_term,immediate2args e') in
      let spec=Specification.mk_spec [] post Specification.ClassMap.empty in
      Assignment_core  ([variable2var (Var_name(n))],spec,[])

  | Var_name v, Reference_exp (Field_local_ref (n,si))  -> 
      (* execute v=n.si --> v:={param0.si|->z}{param0.si|->z * return=z}(n)*)
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      let x = (immediate2args (Immediate_local_name(n))) in 
      let pre=mk_pointsto x (signature2args si) pointed_to_var in
      let post=pconjunction (mkEQ(retvar_term,pointed_to_var)) (mk_pointsto x (signature2args si) pointed_to_var) in
      let spec=Specification.mk_spec pre post Specification.ClassMap.empty in
      Assignment_core ([variable2var (Var_name v)],spec,[])
  | Var_name n, New_simple_exp ty ->
      (* execute x=new(ty) --> x:=null 
	 We treat it as just assigning null to x. This should have the effect
	 to substitute the occurrences of x with a fresh variable. 
	 The rest of the job will be performed by the invocation to specialinvoke <init>
      *)
      translate_assign_stmt (Var_name(n)) (Immediate_exp(Immediate_constant(Null_const)))	
  | Var_name n , Binop_exp(name,x,y)-> 
      let args = Arg_op(Support_syntax.bop_to_prover_arg name, [immediate2args x;immediate2args y]) in
      let post= mkEQ(retvar_term,args) in
      let spec=Specification.mk_spec [] post Specification.ClassMap.empty in
      Assignment_core  ([variable2var (Var_name(n))],spec,[])
  | Var_name n , Cast_exp (_,e') -> (* TODO : needs something for the cast *) 
      translate_assign_stmt (Var_name n) (Immediate_exp(e'))
  | Var_name n , Invoke_exp ie ->  
      let spec,param=get_spec ie in
      Assignment_core ([variable2var (Var_name n)],spec,List.map immediate2args param)
  | _ , _ -> assert false 

let assert_core b =
  match b with
  | Binop_exp (op,i1,i2) -> 
      let b_pred = Support_syntax.bop_to_prover_pred op (immediate2args i1) (immediate2args i2) in
      Assignment_core([], 
		      Specification.mk_spec [] b_pred Specification.ClassMap.empty, 
		      []) 
  | _ -> assert false
  

let jimple_statement2core_statement s : core_statement list =
  match s with 
  | Label_stmt l -> [Label_stmt_core l]
  | Breakpoint_stmt -> assert false
  | Entermonitor_stmt i -> assert false
  | Exitmonitor_stmt i -> assert false
  | Tableswitch_stmt (i,cl) -> assert false
  | Lookupswitch_stmt(i,cl) -> assert false
  | Identity_stmt(nn,id,ty) -> 
      (* nn := id: LinkedLisr   ---> nn:={emp}{return=param0}(id)*)
      if Config.symb_debug() then 
	Printf.printf "\n Translating a jimple identity statement \n  %s\n" (Pprinter.statement2str s);
      let id'=Immediate_local_name(Identifier_name(id)) in 
      let post= mkEQ(retvar_term,immediate2args id') in
      let spec=Specification.mk_spec [] post Specification.ClassMap.empty in
      [Assignment_core  ([variable2var (Var_name(nn))],spec,[]) ]
  | Identity_no_type_stmt(n,i) -> assert false
  | Assign_stmt(v,e) -> 
      if Config.symb_debug() then 
	Printf.printf "\n Translating a jimple assignment statement  %s\n" (Pprinter.statement2str s);
      [translate_assign_stmt v e]
  | If_stmt(b,l) ->
      if Config.symb_debug() 
      then Printf.printf "\n Translating a jimple conditional jump statement  %s\n"  (Pprinter.statement2str s);  
   let l1 = fresh_label () in 
   let l2 = fresh_label () in 
   [Goto_stmt_core([l1;l2]); Label_stmt_core l1; assert_core b; Goto_stmt_core [l];
    Label_stmt_core l2; assert_core (negate b)]
  | Goto_stmt(l) ->
      if Config.symb_debug() then Printf.printf "\n Translating a jimple goto statement  %s\n" (Pprinter.statement2str s);    
      [Goto_stmt_core([l])]
  | Nop_stmt ->  
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Nop statement  %s\n" (Pprinter.statement2str s);    
      [Nop_stmt_core]
  | Ret_stmt(i)  (* return i ---->  ret_var:=i  or as nop operation if it does not return anything*)
  | Return_stmt(i) -> 
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Return statement  %s\n" (Pprinter.statement2str s);    
      (match i with 
       | None -> [Nop_stmt_core]
       | Some e' -> 
	 let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
	 let post= mkEQ(retvar_term,p0) in
	 let spec=Specification.mk_spec [] post Specification.ClassMap.empty in
	 [Assignment_core  ([],spec,[immediate2args e']) ]
      )
  | Throw_stmt(i) ->
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Throw statement %s\n" (Pprinter.statement2str s);      
      [Throw_stmt_core(immediate2args i)]
  | Invoke_stmt (e) -> 
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Invoke statement %s \n" (Pprinter.statement2str s);      
      let spec,param=get_spec e in
      [Assignment_core ([],spec,List.map immediate2args param)]

(* ================   ==================  *)










exception Contained

(* 
recognise if md describes a init method. At the moment it only uses the name. But
maybe we should use a stronger condition
*)
let is_init_method md = Pprinter.name2str md.name_m ="<init>"



let methdec2signature_str dec =
  Pprinter.class_name2str dec.class_name ^ "." ^ Pprinter.name2str dec.name_m ^ "(" ^ (Pprinter.list2str Pprinter.parameter2str  dec.params ", ") ^ ")"


let jimple_methdec2core_body
    (m_jimple: Jimple_global_types.methdec_jimple) = 
  let do_one_stmt stmt_jimple =
    let s=jimple_statement2core_statement stmt_jimple in
    if Config.symb_debug() then 
      Format.printf "@\ninto the core statement:@\n  %a @\n" 
	(Debug.list_format "; " Pprinter_core.pp_stmt_core) s; 
    List.map (fun s -> Methdec_core.stmt_create s [] []) s
  in
  List.flatten (List.map do_one_stmt m_jimple.bstmts)



(* returns a triple (m,initial_formset, final_formset)*)
let get_spec_for m fields cname= 
  let this = mk_this in
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
  let spec=
    try 
      MethodMap.find msi !curr_static_methodSpecs 
    with  Not_found -> 
      System.warning(); Format.printf "\n\n Error: Cannot find spec for method %s\n\n" (methdec2signature_str m); System.reset();
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
    (apfmap : logic Specification.ClassMap.t) 
    (lo : logic) 
    (abs_rules : logic)
    (sspecs: Javaspecs.methodSpecs) 
    (dspecs: Javaspecs.methodSpecs)  =  
  curr_static_methodSpecs:=sspecs;
  curr_dynamic_methodSpecs:=dspecs;
  let cname=Methdec.get_class_name f in
  let lo = try let x=Specification.ClassMap.find (Pprinter.class_name2str cname) apfmap in x with Not_found -> lo in
  let mdl =  Methdec.make_methdecs_of_list cname (Methdec.get_list_methods f) in
  let mdl = List.filter (fun y -> List.for_all (fun x-> Abstract<>x) (y.modifiers)) mdl in
  let fields=Methdec.get_list_fields f in
  let xs = 
    List.map 
      (fun m -> jimple_methdec2core_body m,methdec2signature_str m)
      mdl in (* TODO HERE *)
  Cfg_core.print_icfg_dotty xs (!file);
  List.iter 
    (fun m ->
      let spec = get_spec_for m fields cname in
      let body = jimple_methdec2core_body m in 
      
      Symexec.verify body spec lo abs_rules
      ) mdl

