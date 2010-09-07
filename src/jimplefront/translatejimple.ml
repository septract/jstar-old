(********************************************************
   This file is part of jStar 
	src/jimplefront/translatejimple.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)


open Psyntax
open Jlogic
open Jimple_global_types
open Jparsetree
open Spec_def
open Specification
open Vars
open Support_symex
open Symexec
open Core
open Javaspecs
open Spec

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
	      match (MethodMap.find ms !curr_static_methodSpecs) with
  		      | (spec, pos) -> Some spec 
      with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false

(* retrieve dynamic spec of a method from table of specs*)
let get_dynamic_spec si = 
  match si with 
  | Method_signature ms ->
      (try 
          match (MethodMap.find ms !curr_dynamic_methodSpecs) with
              | (spec, pos) -> Some spec
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
      let subst = Psyntax.add (mk_this) (Arg_var (mk_parameter (List.length il))) Psyntax.empty in 
      sub_spec subst spec,(il@[Immediate_local_name(n)])
  | Invoke_static_exp (si,il) -> 
      spec,il
      



	
let retvar_term = Arg_var(Spec.ret_v1)

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
      let spec=mk_spec pre post ClassMap.empty LabelMap.empty in (* TODO INV *)
      Assignment_core ([],spec,[])	
  | Var_name n, Immediate_exp e' -> 
      (* execute  v=e' --> v:={emp}{return=param0}(e') *)
      let post= mkEQ(retvar_term,immediate2args e') in
      let spec=mk_spec [] post ClassMap.empty LabelMap.empty in (* TODO INV *)
      Assignment_core  ([variable2var (Var_name(n))],spec,[])

  | Var_name v, Reference_exp (Field_local_ref (n,si))  -> 
      (* execute v=n.si --> v:={param0.si|->z}{param0.si|->z * return=z}(n)*)
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      let x = (immediate2args (Immediate_local_name(n))) in 
      let pre=mk_pointsto x (signature2args si) pointed_to_var in
      let post=pconjunction (mkEQ(retvar_term,pointed_to_var)) (mk_pointsto x (signature2args si) pointed_to_var) in
      let spec=mk_spec pre post ClassMap.empty LabelMap.empty in (* TODO INV *)
      Assignment_core ([variable2var (Var_name v)],spec,[])
  | Var_name n, New_simple_exp ty ->
      (* execute x=new(ty)
	 The rest of the job will be performed by the invocation to specialinvoke <init>
      *)
			let post = mk_type_all retvar_term ty in
			let spec = mk_spec [] post ClassMap.empty LabelMap.empty in (* TODO INV *)
			Assignment_core ([variable2var (Var_name n)],spec,[])
  | Var_name n , Binop_exp(name,x,y)-> 
      let args = Arg_op(Support_syntax.bop_to_prover_arg name, [immediate2args x;immediate2args y]) in
      let post= mkEQ(retvar_term,args) in
      let spec=mk_spec [] post ClassMap.empty LabelMap.empty in (* TODO INV *)
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
		      mk_spec [] b_pred ClassMap.empty LabelMap.empty, (* TODO INV *)
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
      let spec=mk_spec [] post ClassMap.empty LabelMap.empty in (* TODO INV *)
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
	 let spec=mk_spec [] post ClassMap.empty LabelMap.empty in (* TODO INV *)
	 [Assignment_core  ([],spec,[immediate2args e']); End ]
      )
  | Throw_stmt(i) ->
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Throw statement %s\n" (Pprinter.statement2str s);      
      [Throw_stmt_core(immediate2args i)]
  | Invoke_stmt (e) -> 
      if Config.symb_debug() then Printf.printf "\n Translating a jimple Invoke statement %s \n" (Pprinter.statement2str s);      
      let spec,param=get_spec e in
      [Assignment_core ([],spec,List.map immediate2args param)]
	| Spec_stmt(vars,spec) -> [Assignment_core (vars,spec,[])]

(* ================   ==================  *)










exception Contained

(* 
recognise if md describes a init method. At the moment it only uses the name. But
maybe we should use a stronger condition
*)
let is_init_method md = Pprinter.name2str md.name_m ="<init>"



let methdec2signature_str dec =
  Pprinter.class_name2str dec.class_name ^ "." ^ Pprinter.name2str dec.name_m ^ "(" ^ (Pprinter.list2str Pprinter.parameter2str  dec.params ", ") ^ ")"
  
  
let jimple_stmt_create s source_pos =
 let node = Cfg_core.mk_node s in
    Printing.source_pos_table := 
      Printing.Source_pos_node_id_table.add 
        node.Cfg_core.sid source_pos 
        !Printing.source_pos_table;
    node 

let jimple_stms2core stms = 
  let do_one_stmt (stmt_jimple, source_pos) =
    let s=jimple_statement2core_statement stmt_jimple in
    if Config.symb_debug() then 
      Format.printf "@\ninto the core statement:@\n  %a @\n" 
      (Debug.list_format "; " Pprinter_core.pp_stmt_core) s; 
    List.map (fun s -> jimple_stmt_create s source_pos) s
  in
  List.flatten (List.map do_one_stmt stms)

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
      match (MethodMap.find msi !curr_static_methodSpecs) with
        | (spec, pos) -> spec
    with  Not_found -> 
      System.warning(); Format.printf "\n\n Error: Cannot find spec for method %s\n\n" (methdec2signature_str m); System.reset();
      assert false
  in
  let spec = logical_vars_to_prog spec in 
  if is_init_method m then (* we treat <init> in a special way*)
    { pre=pconjunction spec.pre class_this_fields; 
      post=spec.post; 
      excep=spec.excep;
      invariants=spec.invariants } (* TODO INV *)
  else spec


let resvar_term = Arg_var(Support_syntax.res_var)

let conjoin_with_res_true (assertion : Psyntax.pform) : Psyntax.pform =
	 pconjunction assertion (mkEQ(resvar_term,Support_symex.constant2args (Int_const (Positive, 1))))

let get_requires_clause_spec_for m fields cname =
        let msi = Methdec.get_msig m cname in
        (* First the the method's dynamic spec *)
        let dynspec = 
                try
                  	match (MethodMap.find msi !curr_dynamic_methodSpecs) with
                        | (spec, pos) -> spec
                with Not_found ->
                        System.warning(); Format.printf "\n\n Error: Cannot find spec for method %s\n\n" (methdec2signature_str m); System.reset();
                        assert false
        in
        let dynspec = logical_vars_to_prog dynspec in
        (* Now construct the desired spec *)
        {
                pre=dynspec.pre;
                post=conjoin_with_res_true (dynspec.pre);
                excep=ClassMap.empty;
                invariants=LabelMap.empty (* TODO INV *)
        }

let get_dyn_spec_for m fields cname =
        let msi = Methdec.get_msig m cname in
        (* First the the method's dynamic spec *)
        let dynspec = 
                try
                  	match (MethodMap.find msi !curr_dynamic_methodSpecs) with
                    	| (spec, pos) -> spec                     
                with Not_found ->
                        System.warning(); Format.printf "\n\n Error: Cannot find spec for method %s\n\n" (methdec2signature_str m); System.reset();
                        assert false
        in
        logical_vars_to_prog dynspec


module LocalMap =
	Map.Make (struct
		type t = string
		let compare = compare
	end)
	
type local_map = Psyntax.args list AxiomMap.t

(*
A jimple method body contains a list of local variable declarations.
One rule is generated for every type appearing in the list.
Example: for type T, suppose v1...vn are all the variables declared of type T.
Then the following rule is generated for T:

rule static_type_T:
 | |- !statictype(?x,"T")
if
 | |- ?x=v1
or
 | |- ?x=v2
...
or
 | |- ?x=vn 
*)
let jimple_locals2stattype_rules (locals : local_var list) : sequent_rule list =
	let localmap = ref (LocalMap.empty) in
	let _ = List.iter (fun (atype,name) ->
		match atype with
			| Some t -> 
					let var = name2args name in
					let typ = Pprinter.j_type2str t in
					(try
						let vars = LocalMap.find typ (!localmap) in
						localmap := LocalMap.add typ (var :: vars) (!localmap)
					with Not_found ->
						localmap := LocalMap.add typ [var] (!localmap)
					)
			| None -> ()
	) locals in
	let x = Arg_var (Vars.fresha ()) in
	LocalMap.fold (fun typ vars rules ->
		let premise : (Psyntax.psequent list list) = List.map (fun var -> [[],[],mkEQ(x,var)]) vars in
		mk_seq_rule (
			([],[],[mk_statictyp1 x (Arg_string typ)]),
			premise,
			"static_type_"^typ
		) :: rules
	) (!localmap) []
	
let add_static_type_info logic locals : Psyntax.logic =
	let rules = jimple_locals2stattype_rules locals in
	Javaspecs.append_rules logic rules
	


(* implements a work-list fidex point algorithm *)
(* the queue qu is a list of pairs [(node, expression option)...] the expression
is used to deal with if statement. It is the expression of the if statement is the predecessor
of the node is a if_stmt otherwise is None. In the beginning is always None for each node *)
let compute_fixed_point 
    (f : Jimple_global_types.jimple_file) 
    (lo : logic) 
    (abs_rules : logic)
    (sspecs: Javaspecs.methodSpecs) 
    (dspecs: Javaspecs.methodSpecs)  =  
  curr_static_methodSpecs:=sspecs;
  curr_dynamic_methodSpecs:=dspecs;
  let cname=Methdec.get_class_name f in
  (* get the method declarations - See make_methdec in methdec.ml *)
  let mdl =  Methdec.make_methdecs_of_list cname (Methdec.get_list_methods f) in
  (* get the fields *)
  let fields = Methdec.get_list_fields f in
    
  (* Adding specification position for init method statements if they do not have their own *)  
  List.iter (fun m ->
    if is_init_method m then
          let mb = List.map (fun (statement, pos) -> 
              match pos with 
                | None -> 
                  let msi = Methdec.get_msig m cname in
                  let spec_pos =
                    try 
                      match (MethodMap.find msi !curr_static_methodSpecs) with
                        | (spec, pos) -> pos
                    with Not_found -> 
                      try 
                        match (MethodMap.find msi !curr_dynamic_methodSpecs) with
                          | (spec, pos) -> pos
                      with  Not_found -> None in
                      (statement, spec_pos)
                | Some _ -> (statement, pos)
            ) m.bstmts in
          m.bstmts <- mb
  ) mdl;
    
  (* pretty print the cfg's *)
  let xs = 
          List.map (fun m ->
                  let meth_sig_str = methdec2signature_str m in
                  let meth_body_info =
                          if Methdec.has_body m then
                                  [(jimple_stms2core m.bstmts, meth_sig_str)]
                          else
                                  []
                  in
                  let requires_info = 
                          if Methdec.has_requires_clause m then
                                  [(jimple_stms2core m.req_stmts, meth_sig_str^" requires clause")]
                          else
                                  []
                  in
                  let old_clause_info = 
                          List.map (fun o -> (jimple_stms2core o,meth_sig_str^" old expression")) m.old_stmts_list
                  in
                  let ensures_info =
                          if Methdec.has_ensures_clause m then
                                  [(jimple_stms2core m.ens_stmts, meth_sig_str^" ensures clause")]
                          else
                                  []
                  in
                  List.flatten [meth_body_info;requires_info;old_clause_info;ensures_info]
          ) mdl in (* TODO HERE *)

  (* Print core files generated from methods *)
  List.iter (fun (x,y) -> Cfg_core.print_core !file y x) (List.flatten xs); 

  (* print dot-file representation of CFG *)
  Cfg_core.print_icfg_dotty (List.flatten xs) (!file);

  (* now verify each method *)
  List.iter (fun m ->
									let meth_sig_str = methdec2signature_str m in
                  (* verify the body only if the method is non-abstract *)
                  if Methdec.has_body m then
                          let spec = get_spec_for m fields cname in
                          let body = jimple_stms2core m.bstmts in
			  let l = add_static_type_info lo m.locals in
			  (*let _ = Prover.pprint_sequent_rules l in*)
                          Symexec.verify meth_sig_str body spec l abs_rules;
                          ()
                  else
                          ()
                  ;
                  (* verify the requires clause if present *)
                  if Methdec.has_requires_clause m then
                          let spec = get_requires_clause_spec_for m fields cname in
                          let body = jimple_stms2core m.req_stmts in
		          let l = add_static_type_info lo m.req_locals in
                          Symexec.verify (meth_sig_str^" requires clause") body spec l abs_rules;
                          ()
                  else
                          ()
                  ;
                  (* verify the ensures clause if present *)
                  if Methdec.has_ensures_clause m then
                          let spec = get_dyn_spec_for m fields cname in
			  let l = add_static_type_info lo m.ens_locals in
                          let frames = List.map (fun oc -> 
                          let body = jimple_stms2core oc in
                          Symexec.get_frame body spec.pre l abs_rules) m.old_stmts_list in
                          let body = jimple_stms2core m.ens_stmts in
                          Symexec.verify_ensures (meth_sig_str^" ensures clause") body spec.post conjoin_with_res_true frames l abs_rules
            ) mdl

