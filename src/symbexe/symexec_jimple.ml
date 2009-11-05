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
      let il = match il with 
	None -> []
      | Some il -> il in
      (* Make this be the final parameter, i.e. subst @this: for @parametern: *) 
      let subst = Pterm.add (mk_this) (Arg_var (mk_parameter (List.length il))) Pterm.empty in 
      sub_spec subst spec,Some (il@[Immediate_local_name(n)])
  | Invoke_static_exp (si,il) -> 
      spec,il
      



	
let retvar_term = Arg_var(ret_var) 

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

      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let post= mkEQ(retvar_term,p0) in
      let spec=Spec_def.mk_spec [] post Spec_def.ClassMap.empty in
      Global_types.Assignment_core  ([Var_name(n)],spec,Some [e'])

  | Var_name v, Reference_exp (Field_local_ref (n,si))  -> 
      (* execute v=n.si --> v:={param0.si|->z}{param0.si|->z * return=z}(n)*)
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let pre=mk_pointsto p0 (signature2args si) pointed_to_var in
      let post=pconjunction (mkEQ(retvar_term,pointed_to_var)) (mk_pointsto p0 (signature2args si) pointed_to_var) in
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
      let p0 = Arg_var(mk_parameter 0) in 
      let p1 = Arg_var(mk_parameter 1) in 
      let args = Arg_op(Support_syntax.bop_to_prover_arg name, [p0;p1]) in
      let post= mkEQ(retvar_term,args) in
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
      let id'=Immediate_local_name(Identifier_name(id)) in 
      let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
      let post= mkEQ(retvar_term,p0) in
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
       | Some e' -> 
	 let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
	 let post= mkEQ(retvar_term,p0) in
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
    let s=jimple_statement2core_statement stmt_jimple.skind in
    if Config.symb_debug() then Printf.printf "\n into the core statement: \n   %s \n" (Pprinter_core.statement_core2str s); 
    Methdec_core.stmt_create s [] [] 
  in
  List.map do_one_stmt m_jimple.bstmts



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
  let xs = 
    List.map 
      (fun m -> jimple_methdec2core_body m,methdec2signature_str m)
      mdl in (* TODO HERE *)
  Cfg_core.print_icfg_dotty xs;
  List.iter 
    (fun m ->
      let spec = get_spec_for m fields cname in
      let body = jimple_methdec2core_body m in 
      
      Symexec.compute_fixed_point body spec lo abs_rules
      ) mdl

