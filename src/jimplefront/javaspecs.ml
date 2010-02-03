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
			let defn = subst_pform sub body in
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
	

let logic_and_implications_for_exports_verification class_name spec_list logic =
	let (_,_,exports_clause,_) = List.find (fun (cn,apf,exports_clause,specs) -> cn=class_name) spec_list in
	match exports_clause with
		| None -> (logic,[])
		| Some (exported_implications,exportLocal_predicates) ->
			let logic = logic_with_where_pred_defs exportLocal_predicates logic in
			(logic,exported_implications) 
			
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
  let (classname,apf,exports_clause,specs) = cs in 
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
      (cn,apf,exports_clause,specs)::sf ->
				let apfs_to_add = if class_name=cn then apf else (List.filter (fun (a,b,x,y,w) -> w) apf) in
				let logic = add_apf_to_logic logic apfs_to_add (Pprinter.class_name2str cn) in 
				add_globals_and_apf_info sf logic
    | [] -> logic
	in add_globals_and_apf_info sf logic



(***************************************
   Refinement type stuff 
 ***************************************)




let refinement_this (logic : logic) (spec1 : spec) (spec2 : spec) (cname : class_name): bool =
    refinement_extra logic spec1 spec2 (objtype this_var (Pprinter.class_name2str cname))


