(********************************************************
   This file is part of jStar 
	src/jimplefront/javaspecs.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)


(* Support functions for symbolic execution and misc conversion facilities *)


open Debug
open Format
open Jimple_global_types
open Jlogic
open Jparsetree
open Psyntax
open Sepprover
open Spec 
open Spec_def
open Specification
open Support_syntax
open System
open Vars

exception Class_defines_external_spec


(* ================ General stuff =================== *)

let append_rules logic rules : Psyntax.logic = 
	let old_rules,rm,f = logic in
	(old_rules @ rules,rm,f)
	
let rec same_elements list =
	match list with
		| [] -> true
		| [_] -> true
		| x::y::zs -> if x=y then same_elements (y::zs) else false  


(* ===================== Augment the logic with apf stuff of a class and exported apfs of other classes  ====================== *)

let apf name receiver params = [P_SPred(name,[Arg_var receiver; mkArgRecord params])]
let apf_match name receiver params = [P_SPred(name,[Arg_var receiver; Arg_var params])]
let not_null1 name = [P_NEQ(name,Arg_op("nil",[]))]
let not_null name = not_null1 (Arg_var name)

exception BadAPF of string

(* Add rules for the relationship between an apf and apf entry, as well as the apf entry and the body *)
let add_apf_to_logic logic apfdefines classname : Psyntax.logic = 
  let make_rules_from_defs (name,receiver,parameters, definition, global) rules = 
(* special variables to match the record as pattern matcher isn't that clever *)
    let recvar = Vars.fresha () in 
    let definition = subst_pform (add receiver (Arg_var recvar) empty)  definition in 
    let paramvar = Vars.fresha () in
    let param_eq = mkEQ(mkArgRecord parameters,Arg_var paramvar) in
(* add resulting equality of definition. *)
    let definition = param_eq&&&definition in
(*    let parvars = VarSet.add receiver (Plogic.fv_fld_list parameters VarSet.empty) in*)
    let parvars = VarSet.add recvar (VarSet.add paramvar VarSet.empty) in
    let defvars = Psyntax.fv_form definition in 
    let sparevars = VarSet.diff defvars parvars in  
    let pvarsubst = subst_kill_vars_to_fresh_prog sparevars in 
    let evarsubst = subst_kill_vars_to_fresh_exist sparevars in 
    let pdefinition = subst_pform pvarsubst definition in 
    let edefinition = subst_pform evarsubst definition in 
    let bodyname = name ^ "$" ^ classname in 
(* open on left *)
    rules @ 
    (mk_seq_rule (([],(objtype recvar classname)&&&(apf_match name recvar paramvar),[]),
		  [[([],((objtype recvar classname)&&&(apf_match bodyname recvar paramvar)),[])]],
		  ("apf_open_left_" ^ name))
     ::
     mk_seq_rule (([],(apf_match bodyname recvar paramvar),[]),
		  [[[],pdefinition,([])]],
		  ("apf_body_left_" ^ name))
     ::
       (* open on right *)
       mk_seq_rule (([], objtype recvar classname, apf_match name recvar paramvar),
		    [[[], objtype recvar classname, apf_match bodyname recvar paramvar]],
		    ("apf_open_right_" ^ name))
     ::
       mk_seq_rule (([],[], apf_match bodyname recvar paramvar),
		    [[[],[],edefinition]],
		    ("apf_body_right_" ^ name))
      ::[])
  in let rec inner apfdefines rules =
    match apfdefines with
      [] -> rules
    | apf::apfdefines -> inner apfdefines (make_rules_from_defs apf rules)
  in 
  let rules,rm,f = logic in 
  let rules = inner apfdefines rules in 
  (rules,rm,f)

let augmented_logic_for_class class_name sf logic =
  let rec add_globals_and_apf_info sf logic = 
    match sf with
      cs::sf ->
				let apfs_to_add = if class_name=cs.classname then cs.apf else (List.filter (fun (a,b,x,y,w) -> w) cs.apf) in
				let logic = add_apf_to_logic logic apfs_to_add (Pprinter.class_name2str cs.classname) in 
				add_globals_and_apf_info sf logic
    | [] -> logic
	in add_globals_and_apf_info sf logic


(* =================== Inheritance relation stuff (classes+interfaces) =================================== *)

(* Returns a list with elements (parent,child) *)
let parent_relation spec_list =
	List.fold_left (fun relation cs ->
		let parents = cs.extends @ cs.implements in (* stephan mult inh *)
		List.fold_left (fun rel p -> (p,cs.classname) :: rel) relation parents
	) [] spec_list
	
let remove_duplicates list =
	List.fold_left (fun rest element -> if List.mem element rest then rest else element :: rest) [] list

let rec transitive_closure relation =
	match relation with
		| [] -> []
		| (ancestor,descendent)::rest ->
			let tr_close_rest = transitive_closure rest in
			if List.mem (ancestor,descendent) tr_close_rest then
				tr_close_rest
			else
				let lower = descendent :: List.map (fun (an,de) -> de) (List.filter (fun (an,de) -> descendent=an) tr_close_rest) in
				let upper = ancestor :: List.map (fun (an,de) -> an) (List.filter (fun (an,de) -> ancestor=de) tr_close_rest) in
				let new_pairs = List.fold_left (fun pairs an ->
						List.fold_left (fun pairs de ->
							(an,de) :: pairs
						) pairs lower
					) [] upper in
				remove_duplicates (new_pairs @ tr_close_rest)

(* Works only if the relation is acyclic, which the inheritance relation should be *)
let rec topological_sort relation =
	match relation with
		| [] -> []
		| _ ->
				let ancestors = remove_duplicates (List.map (fun (an,de) -> an) relation) in
				let no_incoming = List.filter (fun e -> (List.filter (fun (an,de) -> e=de) relation) = []) ancestors in
				if no_incoming = [] then
					assert false (* The relation is cyclic *)
				else
					let pairs,others = List.partition (fun (an,de) -> List.mem an no_incoming) relation in
					let rest = List.filter (fun (_,de) -> (List.filter (fun (a,d) -> a=de || d=de) others) = []) pairs in
					let rest = remove_duplicates (List.map (fun (_,de) -> de) rest) in
					no_incoming @ rest @ (topological_sort others)

(* This returns a list of all classes and interfaces mentioned in spec_file, including those without parents or children *)
let a_topological_ordering_of_all_classes spec_file =
	let pr = parent_relation spec_file in
	let ts = topological_sort pr in
	let others = List.fold_right (fun cs classlist ->
		if List.mem cs.classname ts then
			classlist
		else
			cs.classname :: classlist
		) spec_file [] in
	ts @ others
	
let parent_classes_and_interfaces classname spec_list =
	let cs = List.find (fun cs -> cs.classname=classname) spec_list in
	cs.extends @ cs.implements  (* stephan mult inh *)
	
		

(* =================== Stuff exports and axioms both use ======================== *)

(* The rules for prov => imp, where prov is the implication's proviso *)
let rules_for_implication imp prov : sequent_rule list =
	let name,antecedent,consequent = imp in
	(* imp is assumed to contain only program variables and existential variables *)
	(* to build a rule, we substitute all program variables (but no existentials) with fresh anyvars *)
	let free_vars = Psyntax.fv_form (Psyntax.pconjunction prov (Psyntax.pconjunction antecedent consequent)) in
	let free_prog_vars = VarSet.filter (fun var -> match var with PVar _ -> true | _ -> false) free_vars in
	let sub = VarSet.fold (fun var sub -> add var (Arg_var (Vars.fresha ())) sub) free_prog_vars empty in
	let proviso : Psyntax.pform = subst_pform sub prov in
	let antecedent : Psyntax.pform = subst_pform sub antecedent in
	let consequent = subst_pform sub consequent in
	(* General idea: for Prov => (P ==> (Q1 * Q2 * ... * Qn)), we build n rules of the form *)
	(*  | P |- Qi *)
	(* if *)
	(*  Qi | Q1 * ... * Qi-1 * Qi+1 * ... * Qn |- Prov *)
	(* Should Qi be a P_SPred, then we substitute the anyvars occurring in its 2nd, 3rd etc. arguments with fresh anyvars in the rule's conclusion, *)
	(* and make the anyvar equalities proof obligations in the rule's premise along with Prov. *)
	let split conjuncts =
		let rec split_inner list others =
			match list with
				| [] -> []
				| x :: xs -> (x, xs@others) :: split_inner xs (x::others)
		in
		split_inner conjuncts [] in
	let rules = List.map (fun ((conjunct : Psyntax.pform_at),(others : Psyntax.pform)) ->
			let qi,eqs = match conjunct with
				| P_SPred (pred_name,first_arg :: other_args) -> 
						let freevars = fv_args_list other_args VarSet.empty in
						let free_anyvars = VarSet.filter (fun var -> match var with AnyVar _ -> true | _ -> false) freevars in
						let var_newvar_pairs = VarSet.fold (fun var pairs -> (var,Vars.fresha ()) :: pairs) free_anyvars [] in
						let sub = List.fold_left (fun sub (var,newvar) -> add var (Arg_var newvar) sub) empty var_newvar_pairs in
						let new_other_args = List.map (subst_args sub) other_args in
						let equalities : Psyntax.pform = List.map (fun (var,newvar) -> P_EQ(Arg_var var,Arg_var newvar)) var_newvar_pairs in
						(P_SPred(pred_name,first_arg :: new_other_args),equalities)
				| _ -> (conjunct,[])
			in
			mk_seq_rule (([],antecedent,[qi]),
				[[[conjunct],others,Psyntax.pconjunction eqs proviso]], (* Note the use of conjunct here and not qi. *)
				name)
		) (split consequent) in
	(* Finally, adjust the sequent rule names *)
	let _,rules = List.fold_right (fun (a,b,name,d,e) (counter,list) ->
		(counter-1,(a,b,name^(string_of_int counter),d,e)::list)
	) rules (List.length rules,[]) in
	rules
	

(* =================== Exports clause stuff =============================*)

(* Augment the logic with definitions of the secret 'where' predicates. See paper on exports. *)
let logic_with_where_pred_defs exportLocal_predicates logic =
	List.fold_left (fun logic where_pred_def ->
			let (name, args, body) = where_pred_def in
			let sub = List.fold_left (fun sub argname -> add argname (Arg_var (Vars.fresha ())) sub) empty args in
			let pred = P_SPred(name,List.map (fun argname -> Psyntax.find argname sub) args) in
			let defn = subst_pform sub body in
			let parvars = Psyntax.fv_form [pred] in
			let defvars = Psyntax.fv_form defn  in
			let sparevars = VarSet.diff defvars parvars in  
			let pvarsubst = subst_kill_vars_to_fresh_prog sparevars in 
			let evarsubst = subst_kill_vars_to_fresh_exist sparevars in 
			let pdefinition = subst_pform pvarsubst defn in 
			let edefinition = subst_pform evarsubst defn in
			let rules,rm,f = logic in
			let rules = rules @
				(mk_seq_rule (([],[pred],[]),
					[[[],pdefinition,([])]],
					("exports_body_left_" ^ name))
				::
				mk_seq_rule (([],[],[pred]),
					[[[],[],edefinition]],
					("exports_body_right_" ^ name))
				:: [])
			in
			(rules,rm,f)
		) logic exportLocal_predicates
	
(* Yields the logic augmented with 'where' predicate defs and the implications which are to be checked. *)
let logic_and_implications_for_exports_verification class_name spec_list logic =
	let cs = 
    try
      List.find (fun cs -> cs.classname=class_name) spec_list 
    with Not_found -> failwith 
        ("I need a spec for class " ^ (string_of pp_class_name class_name)) in
	match cs.exports with
		| None -> (logic,[])
		| Some (exported_implications,exportLocal_predicates) ->
			let logic = logic_with_where_pred_defs exportLocal_predicates logic in
			(logic,exported_implications) 
		
(* After exports verification, the exported implications of all classes in the spec file are added to the logic *)
let add_exported_implications_to_logic spec_list logic : Psyntax.logic =
	let exported_implications = List.fold_left (fun imps cs ->
		match cs.exports with
			| None -> imps
			| Some (exported_implications,_) -> exported_implications @ imps
		) [] spec_list in
	let new_rules = List.flatten (List.map (fun imp -> rules_for_implication imp []) exported_implications) in
	append_rules logic new_rules

(* ============================= Axioms clause stuff ================================ *)

module AxiomMap =
	Map.Make (struct
		type t = class_name * string  (* the class name and axiom name *)
		let compare = compare
	end)
	
type axiom_map = (Psyntax.pform * Psyntax.pform) AxiomMap.t

let filtermap filterfun mapfun list =
	List.map mapfun (List.filter filterfun list)
	
let axiommap_filter p axiommap =
	AxiomMap.fold (fun key value result -> if p key value then AxiomMap.add key value result else result) axiommap AxiomMap.empty
	
let axiommap2list f axiommap =
	AxiomMap.fold (fun key value list -> f key value :: list) axiommap []

let spec_file_to_axiom_map spec_list =
	let axiommap = ref (AxiomMap.empty) in
	let _ = List.iter (fun cs ->
		match cs.axioms with
			| None -> ()
			| Some imps ->
					List.iter (fun (name,antecedent,consequent) -> 
						axiommap := AxiomMap.add (cs.classname,name) (antecedent,consequent) (!axiommap)
					) imps
	) spec_list in
	(* Add inherited axioms *)
	let pr = parent_relation spec_list in
	let ts = topological_sort pr in
	let _ = List.iter (fun classname ->
		let parents = parent_classes_and_interfaces classname spec_list in
		let parent_axiom_map = axiommap_filter (fun (cn,an) imp -> List.mem cn parents) (!axiommap) in
		let parent_axiom_names = remove_duplicates (axiommap2list (fun (cn,an) _ -> an) parent_axiom_map) in
		List.iter (fun axiom_name ->
			try
				let _ = AxiomMap.find (classname,axiom_name) (!axiommap) in ()
			with Not_found ->
				let parent_axioms_with_same_name = axiommap2list (fun k imp -> imp) (axiommap_filter (fun (cn,an) ni -> an = axiom_name) parent_axiom_map) in
				if same_elements parent_axioms_with_same_name then
					()
				else if Config.symb_debug () then
                                  printf 
                                      "@{<b>WARNING:@} %s does not list axiom \
                                          %s and its parents do not have the \
                                          same spec for it!@."
                                      (Pprinter.class_name2str classname) 
                                      axiom_name;
				match parent_axioms_with_same_name with
					| x :: xs -> axiommap := AxiomMap.add (classname,axiom_name) x (!axiommap)
					| _ -> assert false
		) parent_axiom_names
	) ts in
	!axiommap

let implications_for_axioms_verification class_name axiom_map : named_implication list =
	let axioms = axiommap_filter (fun (cn,an) imp -> cn=class_name) axiom_map in
	axiommap2list (fun (cn,an) (ant,con) -> (an,ant,con)) axioms

module AxiomMap2 =
	Map.Make (struct
		type t = class_name
		let compare = compare
	end)
	
type axiom_map2 = named_implication list AxiomMap2.t

let spec_file_to_axiom_map2 spec_list =
	let axiommap = ref (AxiomMap2.empty) in
	let _ = List.iter (fun cs ->
		match cs.axioms with
			| None -> axiommap := AxiomMap2.add cs.classname [] (!axiommap)
			| Some imps -> axiommap := AxiomMap2.add cs.classname imps (!axiommap)
	) spec_list in
	!axiommap

(* Add the axioms of all classes in the spec file to the logic *)
let add_axiom_implications_to_logic spec_list logic : Psyntax.logic = 
	let classlist = a_topological_ordering_of_all_classes spec_list in
	let axiommap = spec_file_to_axiom_map2 spec_list in
	let new_rules = List.fold_right (fun cl rules ->
		try
			let named_imps : named_implication list = AxiomMap2.find cl axiommap in
			let proviso = [mk_objsubtyp (Arg_var this_var) cl] in
			let clname = Pprinter.class_name2str cl in
			let new_rules = List.fold_right (fun (n,a,c) ruls ->
				let freevars = Psyntax.fv_form (Psyntax.pconjunction a c) in
				let p = if VarSet.mem this_var freevars then proviso else [] in 
				rules_for_implication ("axiom_"^clname^"_"^n,a,c) p
				@ ruls) named_imps [] in
			new_rules @ rules
		with Not_found -> assert false
	) classlist [] in
	append_rules logic new_rules
	

(* ====================== Method spec manipulation and completion ====================================== *)

let is_interface classname spec_list =
	let cs = List.find (fun cs -> cs.classname=classname) spec_list in
	match cs.class_or_interface with
		| InterfaceFile -> true
		| ClassFile -> false

let is_method_abstract (method_signature : method_signature) spec_list =
	let cn,rt,name,params = method_signature in
	let cs = List.find (fun cs -> cs.classname=cn) spec_list in
	try
		let _ = List.find (fun ms ->
			match ms with
				| Spec_def.Static ((_,ty,mn,ps),_) -> ty=rt && mn=name && ps=params
				| _ -> false
		) cs.methodspecs in
		false
	with Not_found ->
		try
			let _ = List.find (fun ms ->
				match ms with
					| Spec_def.Dynamic ((mods,ty,mn,ps),_) -> ty=rt && mn=name && ps=params && List.mem Jparsetree.Abstract mods
					| _ -> false
			) cs.methodspecs in
			true
		with Not_found -> false (* By default, a method is non-abstract *)

module MethodMap = 
  Map.Make(struct
    type t = method_signature
    let compare = compare
  end)
module MethodMapH = Misc.MapHelper (MethodMap)

module MethodSet = 
  Set.Make(struct
    type t = method_signature
    let compare = compare
  end)

type methodSpecs = spec MethodMap.t

let emptyMSpecs : methodSpecs = MethodMap.empty
let addMSpecs msig spec mmap : methodSpecs = MethodMap.add msig spec mmap

let rec spec_list_to_spec specs = 
   match specs with 
   | [] -> assert false  (* Should get here *)
   | [spec] -> spec
   | spec :: specs ->
       spec_conjunction spec (spec_list_to_spec specs)
 
let class_spec_to_ms cs (smmap,dmmap) =
  let cn = (*Pprinter.class_name2str*) cs.classname in
  List.fold_left 
    (fun (smmap,dmmap) pre_spec
      -> 
	match pre_spec with 
	  Dynamic (ms,spec) -> 
	    (match ms with 
	      (mods,a,b,c) -> 
		(smmap,addMSpecs (cn,a,b,c) (spec_list_to_spec spec) dmmap)
	    )
	| Spec_def.Static (ms,spec) -> 
	    (match ms with 
	      (mods,a,b,c) -> 
		(addMSpecs (cn,a,b,c) (spec_list_to_spec spec) smmap,dmmap)
	    )
    ) 
    (smmap,dmmap) cs.methodspecs 


let remove_this_type_info prepure = 
  let is_this_type p = 
    match p with 
      P_PPred (name,a::al) -> if name = objtype_name  && a = (Arg_var (Vars.concretep_str this_var_name)) then false else true
    | _ -> true 
  in List.filter is_this_type prepure

let static_to_dynamic {pre=pre; post=post; excep=excep; invariants=invariants} =
  { pre=remove_this_type_info pre; 
    post=post; 
    excep=excep; 
    invariants=invariants (* TODO INV *) }

let rec filtertype_spat classname spat =
  match spat with
    P_SPred(name,t1::ar::[])  -> 
      (try 
	if t1=Arg_var(this_var) && ((String.rindex name '$') = (String.length name) -1 ) then 
	  P_SPred(name ^ classname, t1::ar::[]) 
	else spat
      with Not_found -> spat)
  | P_SPred(name,al) -> P_SPred(name,al)
  | P_Or(form1,form2) -> P_Or(filtertype classname form1, filtertype classname form2)
  | P_Wand (form1,form2) -> P_Wand(filtertype classname form1, filtertype classname form2)
  | P_Septract (form1,form2) -> P_Septract(filtertype classname form1, filtertype classname form2)
  | P_Garbage -> P_Garbage
  | P_False -> P_False
  | P_PPred(name,al) -> spat
  | P_EQ(_,_) -> spat
  | P_NEQ(_,_) -> spat
and filtertype classname = List.map (filtertype_spat classname ) 

let rec filterdollar_at spat =
  match spat with
    P_SPred(name,t1::ar::[])  -> 
      (try 
	if t1=Arg_var(this_var) && ((String.rindex name '$') = (String.length name) -1 ) then 
	  P_SPred(String.sub name 0 (String.length name - 1), t1::ar::[]) 
	else spat
      with Not_found -> spat)
  | P_SPred(name,al) -> P_SPred(name,al)
  | P_PPred(name,al) -> spat
  | P_Or(form1,form2) -> P_Or(filterdollar form1, filterdollar form2)
  | P_Wand (form1,form2) -> P_Wand(filterdollar form1, filterdollar form2)
  | P_Septract (form1,form2) -> P_Septract(filterdollar form1, filterdollar form2)
  | P_Garbage -> P_Garbage
  | P_False -> P_False
  | P_EQ(_,_) -> spat
  | P_NEQ(_,_) -> spat
and filterdollar x = List.map (filterdollar_at) x


let dynamic_to_static cn spec = 
  match spec with
    {pre=f1; post=f2; excep=excep; invariants=invariants}
      -> {pre=filtertype cn f1; 
	  post=filtertype cn f2; 
	  excep=ClassMap.map (filtertype cn) excep;
          invariants=LabelMap.map (filtertype cn) invariants (* TODO INV *) }

let filter_dollar_spec {pre=f1; post=f2; excep=excep; invariants=invariants} =
  { pre=filterdollar f1; 
    post=filterdollar f2; 
    excep=ClassMap.map filterdollar excep;
    invariants=LabelMap.map filterdollar invariants (* TODO INV *) }

let fix_spec_inheritance_gaps classes mmap spec_file exclude_function spec_type =
	let mmapr = ref mmap in
	let rec propagate_specs cn specs_parents =
		match specs_parents with
			| [] -> ()
			| (rt,name,params,spec)::others ->
					let samesig,othersigs = List.partition (fun (a,b,c,d) -> rt=a && name=b && params=c) ((rt,name,params,spec)::others) in
					let msig = (cn,rt,name,params) in
					let _ = if MethodMap.mem msig (!mmapr) || Jparsetree.constructor name || exclude_function msig then
										()
									else
										if same_elements samesig then
											mmapr := MethodMap.add msig spec (!mmapr)
										else
											if
                                                                                          Config.symb_debug()
                                                                                then
                                                                                  printf "@{<b>WARNING:@} There is no %s spec listed for %s, and its parents do not agree on one!\n" spec_type (Pprinter.signature2str (Method_signature msig));
					in
					propagate_specs cn othersigs  
	in
	let rec fix_inner classes =
		match classes with
			| [] -> ()
			| cn :: classes ->
					let parents = parent_classes_and_interfaces cn spec_file in
					let specs_parents = MethodMap.fold (fun (classname,a,b,c) spec list -> if List.mem classname parents then (a,b,c,spec)::list else list) (!mmapr) [] in
					let _ = propagate_specs cn specs_parents in  
					fix_inner classes
	in
	let _ = fix_inner classes in
	!mmapr

let fix_gaps (smmap,dmmap) spec_file =
	(* Firstly, we derive dynamic from static specs and vice versa. *)
  let dmmapr = ref dmmap in 
  let smmapr = ref smmap in 
  let _ = MethodMap.iter 
      (fun key spec -> 
	if MethodMap.mem key (!dmmapr) then () else dmmapr := MethodMap.add key (static_to_dynamic spec) (!dmmapr)
      ) smmap in
  let _ = MethodMap.iter 
      (fun (cn,a,b,c) spec -> 
	if MethodMap.mem (cn,a,b,c) (!smmapr) || is_interface cn spec_file || is_method_abstract (cn,a,b,c) spec_file then () 
	else
		smmapr := MethodMap.add (cn,a,b,c) (dynamic_to_static (Pprinter.class_name2str cn) spec) (!smmapr);
		dmmapr := MethodMap.add (cn,a,b,c) (filter_dollar_spec spec) !dmmapr
  ) dmmap in
	(* Secondly, we fix the gaps created by inheritance *)
	let classes = topological_sort (parent_relation spec_file) in
	let _ = dmmapr := fix_spec_inheritance_gaps classes (!dmmapr) spec_file (fun _ -> false) "dynamic" in
	let _ = smmapr := fix_spec_inheritance_gaps classes (!smmapr) spec_file (fun msig -> is_method_abstract msig spec_file) "static" in
  (!smmapr,!dmmapr)


let spec_file_to_method_specs 
    (sf : Spec_def.class_spec list) : (methodSpecs * methodSpecs) =
  let rec sf_2_ms_inner sf (pairmmap) = 
    match sf with 
      [] -> pairmmap
    | cs::sf -> sf_2_ms_inner sf (class_spec_to_ms cs pairmmap)
  in fix_gaps (sf_2_ms_inner sf (emptyMSpecs,emptyMSpecs)) sf


(* ========================== Common/useful rules ================================ *)

	
let mk_subeq (var1,var2) = [P_PPred("subeq",[Arg_var var1;Arg_var var2])]
let mk_sub (var1,var2) = [P_PPred("sub",[Arg_var var1;Arg_var var2])]

(*
A rule for subeq is generated:
 | |- !subeq(?x,?y)
if
 | |- ?x=?y
or
 | |- !sub(?x,?y)
 
For every p being an apf predicate P or apf entry P$C, a matching rule will be generated:
 | p(?x,?y) |- p(?x,?z)
if
 p(?x,?y) | |- !subeq(?y,?z)

Furthermore, for every apf predicate P, two non-null rules are generated:
 | P(?x,?y) |- ?x!=nil()
if
 | P(?x,?y) |-

and

 P(?x,?y) | |- ?x!=nil()
if
 P(?x,?y) | |-
*) 
let add_common_apf_predicate_rules spec_list logic =
	let make_apf = apf_match in
	let add_if_not_there element list = if List.mem element list then list else element::list in
	let apf_preds,apf_entries = List.fold_left (fun (apf_preds,apf_entries) cs ->
		let classname = Pprinter.class_name2str cs.classname in
		List.fold_left (fun (apf_preds,apf_entries) (name,receiver,parameters,_,_) ->
			(add_if_not_there name apf_preds,(name^"$"^classname)::apf_entries)
		) (apf_preds,apf_entries) cs.apf
	) ([],[]) spec_list in
	let recvar = Vars.fresha() in
	let param = Vars.fresha() in
	let param' = Vars.fresha() in
	let subeq_rule =
		mk_seq_rule (([],[],mk_subeq(param,param')),
			[[([],[],mkEQ(Arg_var param,Arg_var param'))];[([],[],mk_sub(param,param'))]],
			"subeq_rule"
		)
	in
	let match_rules = List.map (fun predname ->
		let left = make_apf predname recvar param in
		let right = make_apf predname recvar param' in
		mk_seq_rule (([],left,right),
			[[left,[],mk_subeq(param,param')]],
			(predname^"_match")
		)
	) (apf_preds @ apf_entries) in
	let not_null_rules = List.fold_left (fun rules predname ->
		let form = make_apf predname recvar param in
		(mk_seq_rule (([],form,not_null recvar),
			[[[],form,[]]],
			(predname^"_not_nil1")
		 ) ::
		 mk_seq_rule ((form,[],not_null recvar),
			[[form,[],[]]],
			(predname^"_not_nil2")
		 ) :: rules)
	) [] apf_preds in
	append_rules logic (subeq_rule::(match_rules @ not_null_rules))

(*
Adds a rule containing the transitive subtype relation, as well as one to reason 
about whether an object is an instance (but not neccessarily a direct instance) of a type.

For the first rule, if C inherits from B, which in turn inherits from A, then the following gets generated:

rule subtype_relation_right:
 | |- !subtype(?x,?y)
if
 | |- ?x=?y
or
 | |- ?x="C" * ?y="B"
or
 | |- ?x="B" * ?y="A"
or
 | |- ?x="C" * ?y="A"

Here is the second rule:

rule objsubtype_right:
 | |- !objsubtype(?o,?c)
if
 | |- !type(?o,?d) * !subtype(?d,?c)
or
 | |- ?o!=nil() * !stattype(?o,_e) * !subtype(_e,?c)
| 
*)
let add_subtype_and_objsubtype_rules spec_list logic =
	let pr = parent_relation spec_list in
	let tc = transitive_closure pr in
	let x = Arg_var (Vars.fresha ()) in
	let y = Arg_var (Vars.fresha ()) in
	let premise : (Psyntax.psequent list list) = 
		[([],[],mkEQ(x,y))] ::
		List.map (fun (ancestor,descendent) -> [[],[],[P_EQ(x,Jlogic.class2args descendent);P_EQ(y,Jlogic.class2args ancestor)]]) tc in
	let subtype_rule = mk_seq_rule (([],[],Jlogic.mk_subtype1 x y),premise,"subtype_relation_right") in
	let o = Arg_var (Vars.fresha ()) in
	let c = Arg_var (Vars.fresha ()) in
	let d = Arg_var (Vars.fresha ()) in
	let e = Arg_var (Vars.freshe ()) in
	let objsubtype_rule = mk_seq_rule (
		([],[],[Jlogic.mk_objsubtyp1 o c]),
		[[([],[],(Jlogic.mk_type1 o d) @ (Jlogic.mk_subtype1 d c))];
		 [([],[],(not_null1 o) @ (Jlogic.mk_statictyp1 o e :: Jlogic.mk_subtype1 e c))]],
		"objsubtype_right"
	) in
	append_rules logic [objsubtype_rule;subtype_rule]
	


(* ====================== Refinement type stuff ================================= *)


let refinement_this (logic : logic) (spec1 : spec) (spec2 : spec) (cname : class_name): bool =
(*DBG  Format.fprintf Format.err_formatter "@[<2>===first===@\n";
  spec2str Format.err_formatter spec1;
  Format.fprintf Format.err_formatter "@]@\n@[<2>===second===@\n";
  spec2str Format.err_formatter spec2;
  Format.fprintf Format.err_formatter "@]@."; *)
  refinement_extra logic spec1 spec2 (objtype this_var (Pprinter.class_name2str cname))


