(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(* Support functions for simbolic execution and misc conversion facilities *)


open Vars
open Rterm
open Pterm
open Plogic
open Spec_def
open Global_types
open Jlogic
open Jparsetree
open Prover
open Support_syntax
open Specification

exception Class_defines_external_spec



let apf name receiver params = [P_SPred(name,[Arg_var receiver; mkArgRecord params])]
let apf_match name receiver params = [P_SPred(name,[Arg_var receiver; Arg_var params])]
let not_null name = [P_NEQ(Arg_var name,Arg_op("nil",[]))]

exception BadAPF of string
(* TODO APF to logic *)
let add_apf_to_logic logic apfdefines classname : Prover.logic = 
  let make_rules_from_defs (name,receiver,parameters, definition, global) rules = 
(* special variables to match the record as pattern matcher isn't that clever *)
    let recvar = Vars.fresha () in 
    let definition = subst_pform (add receiver (Arg_var recvar) empty)  definition in 
    let paramvar = Vars.fresha () in
    let paramvar' = Vars.fresha () in
    let param_eq = mkEQ(mkArgRecord parameters,Arg_var paramvar) in
(* add resulting equality of definition. *)
    let definition = param_eq&&&definition in
(*    let parvars = VarSet.add receiver (Plogic.fv_fld_list parameters VarSet.empty) in*)
    let parvars = VarSet.add recvar (VarSet.add paramvar VarSet.empty) in
    let defvars = Plogic.fv_form definition VarSet.empty in 
    let sparevars = VarSet.diff defvars parvars in  
(*TODO: The following sanity checks need rewriting to deal with the new rule form *)
(*    let _ = if VarSet.for_all (fun x-> match x with EVar _ -> true | _ -> false) sparevars then () else raise ( BadAPF("Variable escape")) in 
    let _ = if VarSet.cardinal parvars = List.length parameters +1 then () else raise (BadAPF "Parameters not distinct") in *)
    (*Printf.printf "\n\nAdding a pair of apf rules for %s in class %s.\n" name classname;*)
    let pvarsubst = subst_kill_vars_to_fresh_prog sparevars in 
    let evarsubst = subst_kill_vars_to_fresh_exist sparevars in 
    let pdefinition = try subst_pform pvarsubst definition with Contradiction -> mkFalse in 
    let edefinition = try subst_pform evarsubst definition with Contradiction -> mkFalse in 
    let bodyname = name ^ "$" ^ classname in 
(* open on left *)
    rules @ 
    (mk_seq_rule (([],(objtype recvar classname)&&&(apf_match name recvar paramvar),[]),
		  [[([],((objtype recvar classname)&&&(apf_match bodyname recvar paramvar)),[])]],
		  ("apf_open_left_" ^ name))
     ::
     mk_seq_rule (((apf_match name recvar paramvar),[],not_null recvar),
		  [[([],[],[])]],
		  ("apf_not_nil_" ^ name))
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
     ::
       mk_seq_rule (([],apf_match name recvar paramvar, apf_match name recvar paramvar'),
		    [[apf_match name recvar paramvar,[],[P_SPred("subeq",[Arg_var paramvar;Arg_var paramvar'])]]],
		    ("apf_match_" ^ name))
     ::
       mk_seq_rule (([],apf_match bodyname recvar paramvar, apf_match bodyname recvar paramvar'),
		    [[apf_match bodyname recvar paramvar,[],[P_SPred("subeq",[Arg_var paramvar;Arg_var paramvar'])]]],
		    ("apf_match_" ^ name))
      ::[])
  in let rec inner apfdefines rules =
    match apfdefines with
      [] -> rules
    | apf::apfdefines -> inner apfdefines (make_rules_from_defs apf rules)
  in 
  let rules,rm,f = logic in 
  let rules = inner apfdefines rules in 
  (rules,rm,f)

let logic_with_where_pred_defs exportLocal_predicates logic =
	List.fold_left (fun logic where_pred_def ->
			let (name, args, body) = where_pred_def in
			let sub = List.fold_left (fun sub argname -> add argname (Arg_var (Vars.fresha ())) sub) empty args in
			let pred = P_SPred(name,List.map (fun argname -> Pterm.find argname sub) args) in
			let defn = try subst_pform sub body with Contradiction -> mkFalse in
			let parvars = Plogic.fv_form [pred] VarSet.empty in
			let defvars = Plogic.fv_form defn VarSet.empty in
			let sparevars = VarSet.diff defvars parvars in  
			let pvarsubst = subst_kill_vars_to_fresh_prog sparevars in 
			let evarsubst = subst_kill_vars_to_fresh_exist sparevars in 
			let pdefinition = try subst_pform pvarsubst defn with Contradiction -> mkFalse in 
			let edefinition = try subst_pform evarsubst defn with Contradiction -> mkFalse in
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

let rules_for_implication imp : Prover.sequent_rule list =
	let name,antecedent,consequent = imp in
	(* imp is assumed to contain only program variables and existential variables *)
	(* to build a rule, we substitute all program variables (but no existentials) with fresh anyvars *)
	let free_vars = Plogic.fv_form (Plogic.pconjunction antecedent consequent) VarSet.empty in
	let free_prog_vars = VarSet.filter (fun var -> match var with PVar _ -> true | _ -> false) free_vars in
	let sub = VarSet.fold (fun var sub -> add var (Arg_var (Vars.fresha ())) sub) free_prog_vars empty in
	let antecedent : Plogic.pform = try subst_pform sub antecedent with Contradiction -> mkFalse in
	let consequent = try subst_pform sub consequent with Contradiction -> mkFalse in
	(* General idea: for P ==> (Q1 * Q2 * ... * Qn), we build n rules of the form *)
	(*  | P |- Qi *)
	(* if *)
	(*  Qi | Q1 * ... * Qi-1 * Qi+1 * ... * Qn |- *)
	(* Should Qi be a P_SPred, then we substitute the anyvars occurring in its 2nd, 3rd etc. arguments with fresh anyvars in the rule's conclusion, *)
	(* and make the anyvar equalities proof obligations in the rule's premise. *)
	let split conjuncts =
		let rec split_inner list others =
			match list with
				| [] -> []
				| x :: xs -> (x, xs@others) :: split_inner xs (x::others)
		in
		split_inner conjuncts [] in
	let rules = List.map (fun ((conjunct : Plogic.pform_at),(others : Plogic.pform)) ->
			let qi,eqs = match conjunct with
				| P_SPred (pred_name,first_arg :: other_args) -> 
						let freevars = fv_args_list other_args VarSet.empty in
						let free_anyvars = VarSet.filter (fun var -> match var with AnyVar _ -> true | _ -> false) freevars in
						let var_newvar_pairs = VarSet.fold (fun var pairs -> (var,Vars.fresha ()) :: pairs) free_anyvars [] in
						let sub = List.fold_left (fun sub (var,newvar) -> add var (Arg_var newvar) sub) empty var_newvar_pairs in
						let new_other_args = List.map (subst_args sub) other_args in
						let equalities : Plogic.pform =
                                                        List.map (fun
                                                                (var,newvar) -> P_EQ(Arg_var var,Arg_var newvar)) var_newvar_pairs in
						(P_SPred(pred_name,first_arg :: new_other_args),equalities)
				| _ -> (conjunct,[])
			in
			mk_seq_rule (([],antecedent,[qi]),
				[[[conjunct],others,eqs]], (* Note the use of conjunct here and not qi. *)
				name)
		) (split consequent) in
	(* Finally, adjust the sequent rule names *)
	let _,rules = List.fold_right (fun (a,b,name,d,e) (counter,list) ->
		(counter-1,(a,b,name^(string_of_int counter),d,e)::list)
	) rules (List.length rules,[]) in
	rules

let add_implications_to_logic (logic : Prover.logic) imps : Prover.logic =
	let new_rules = List.flatten (List.map (fun imp -> rules_for_implication imp) imps) in
	let rules,rm,f = logic in
	(rules @ new_rules,rm,f)

let logic_and_implications_for_exports_verification class_name spec_list logic =
	let (_,_,exports_clause,_,_) = List.find (fun (cn,apf,exports_clause,axioms_clause,specs) -> cn=class_name) spec_list in
	match exports_clause with
		| None -> (logic,[])
		| Some (exported_implications,exportLocal_predicates) ->
			let logic = logic_with_where_pred_defs exportLocal_predicates logic in
			(logic,exported_implications) 
			
let add_exported_implications_to_logic spec_list logic : Prover.logic =
	let exported_implications = List.fold_left (fun imps (cn,apf,exports_clause,axioms_clause,specs) ->
		match exports_clause with
			| None -> imps
			| Some (exported_implications,_) -> exported_implications @ imps
		) [] spec_list in
	add_implications_to_logic logic exported_implications


let implications_for_axioms_verification class_name spec_list =
	let (_,_,_,axioms_clause,_) = List.find (fun (cn,apf,exports_clause,axioms_clause,specs) -> cn=class_name) spec_list in
	match axioms_clause with
		| None -> []
		| Some named_implications -> named_implications

module AxiomMap =
	Map.Make (struct
		type t = class_name * string  (* the class name and axiom name *)
		let compare = compare
	end)
	
type axiom_map = (Plogic.pform * Plogic.pform) AxiomMap.t

let spec_file_to_axiom_map spec_list =
	let axiommap = ref (AxiomMap.empty) in
	let _ = List.iter (fun (cn,_,_,axioms_clause,_) ->
		match axioms_clause with
			| None -> ()
			| Some imps ->
					List.iter (fun (name,antecedent,consequent) -> 
						axiommap := AxiomMap.add (cn,name) (antecedent,consequent) (!axiommap)
					) imps
	) spec_list in
	!axiommap

(* Specs to verification *)

module MethodMap = 
  Map.Make(struct
    type t = method_signature
    let compare = compare
  end)

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
  let (classname,apf,exports_clause,axioms_clause,specs) = cs in 
  let cn = (*Pprinter.class_name2str*) classname in
  List.fold_left 
    (fun (smmap,dmmap) pre_spec
      -> 
	match pre_spec with 
	  Dynamic (ms,spec) -> 
	    (match ms with 
	      (a,b,c) -> 
		(smmap,addMSpecs (cn,a,b,c) (spec_list_to_spec spec) dmmap)
	    )
	| Spec_def.Static (ms,spec) -> 
	    (match ms with 
	      (a,b,c) -> 
		(addMSpecs (cn,a,b,c) (spec_list_to_spec spec) smmap,dmmap)
	    )
    ) 
    (smmap,dmmap) specs 


let remove_this_type_info prepure = 
  let is_this_type p = 
    match p with 
      P_PPred (name,a::al) -> if name = objtype_name  && a = (Arg_var (Vars.concretep_str this_var_name)) then false else true
    | _ -> true 
  in List.filter is_this_type prepure

let static_to_dynamic spec = 
  match spec with 
    {pre=pre; post=post; excep=excep} 
      ->  {pre=remove_this_type_info pre; post=post; excep=excep}

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
    {pre=f1; post=f2; excep=excep}
      -> {pre=filtertype cn f1; 
	  post=filtertype cn f2; 
	  excep=ClassMap.map (filtertype cn) excep}

let filter_dollar_spec spec = 
  match spec with
    {pre=f1; post=f2; excep=excep}
      -> {pre=filterdollar f1; 
	  post=filterdollar f2; 
	  excep=ClassMap.map filterdollar excep}

let fix_gaps (smmap,dmmap) =
  let dmmapr = ref dmmap in 
  let smmapr = ref smmap in 
  let _ = MethodMap.iter 
      (fun key spec -> 
	if MethodMap.mem key (!dmmapr) then () else dmmapr := MethodMap.add key (static_to_dynamic spec) (!dmmapr)
      ) smmap in
  let _ = MethodMap.iter 
      (fun (cn,a,b,c) spec -> 
	if MethodMap.mem (cn,a,b,c) (!smmapr) then () 
	else smmapr := MethodMap.add (cn,a,b,c) (dynamic_to_static (Pprinter.class_name2str cn) spec) (!smmapr);
	dmmapr := MethodMap.add (cn,a,b,c) (filter_dollar_spec spec) !dmmapr
      ) dmmap in
  (!smmapr,!dmmapr)


let spec_file_to_method_specs sf =
  let rec sf_2_ms_inner sf (pairmmap) = 
    match sf with 
      [] -> pairmmap
    | cs::sf -> sf_2_ms_inner sf (class_spec_to_ms cs pairmmap)
  in fix_gaps (sf_2_ms_inner sf (emptyMSpecs,emptyMSpecs))


let augmented_logic_for_class class_name sf logic =
  let rec add_globals_and_apf_info sf logic = 
    match sf with
      (cn,apf,exports_clause,axioms_clause,specs)::sf ->
				let apfs_to_add = if class_name=cn then apf else (List.filter (fun (a,b,x,y,w) -> w) apf) in
				let logic = add_apf_to_logic logic apfs_to_add (Pprinter.class_name2str cn) in 
				add_globals_and_apf_info sf logic
    | [] -> logic
	in add_globals_and_apf_info sf logic


(*
For every class C and for each apf predicate P(x,{t1=a1;...;tn=an}) defined in C,
two rules are generated by add_common_apf_predicate_rules:

C_P_same:
 | P(?x,{t1=?a1;...;tn=?an}) |- P(?x,{t1=?b1;...;tn=?bn})
if
 P(?x,{t1=?a1;...;tn=?an}) | |- ?a1=?b1 * ... * ?an=?bn

P_C_same:
 | P$C(?x,{t1=?a1;...;tn=?an}) |- P$C(?x,{t1=?b1;...;tn=?bn})
if
 P$C(?x,{t1=?a1;...;tn=?an}) | |- ?a1=?b1 * ... * ?an=?bn
*)
let add_common_apf_predicate_rules spec_list logic =
	let make_apf = apf in
	let recvar = Vars.fresha () in
	let deep_rules = List.map (fun (classname,apf,exports,axioms,specs) ->
		let classname = Pprinter.class_name2str classname in
		List.map (fun ((name,receiver,parameters, definition, global) : Spec_def.apf_define) ->
			let args1,args2,eqs = List.fold_right (fun (fld,arg) (args1,args2,eqs) ->
				let arg1 = Arg_var (Vars.fresha ()) in
				let arg2 = Arg_var (Vars.fresha ()) in
				((fld,arg1)::args1, (fld,arg2)::args2, P_EQ(arg1,arg2)::eqs)
			) parameters ([],[],[]) in
			let apf_pred1 = make_apf name recvar args1 in
			let apf_pred2 = make_apf name recvar args2 in
			let apf_entry1 = make_apf (name^"$"^classname) recvar args1 in
			let apf_entry2 = make_apf (name^"$"^classname) recvar args2 in
			(mk_seq_rule (([],apf_pred1,apf_pred2),
				[[apf_pred1,[],eqs]],
				(classname^"_"^name^"_same"))
			 ::
			 mk_seq_rule (([],apf_entry1,apf_entry2),
				[[apf_entry1,[],eqs]],
				(name^"_"^classname^"_same"))
			 :: [])
		) apf
	) spec_list in
	let rules = List.flatten (List.flatten deep_rules) in
	let old_rules,rm,f = logic in 
  let new_rules = old_rules @ rules in 
  (new_rules,rm,f)


(***************************************
   Refinement type stuff 
 ***************************************)




let refinement_this (logic : logic) (spec1 : spec) (spec2 : spec) (cname : class_name): bool =
    refinement_extra logic spec1 spec2 (objtype this_var (Pprinter.class_name2str cname))


