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
open Global_types
open Jlogic
open Jparsetree
open Prover

exception Class_defines_external_spec

(*
module ClassMap =   
  Map.Make(struct
    type t = class_name
    let compare = compare
  end)
*)

type java_exception = class_name

(*type excep_post = representative Plogic.pform ClassMap.t  *)

type ts_excep_post = Rlogic.ts_form ClassMap.t 

let conjunction_excep excep_post f1 =
  ClassMap.map (fun post -> Plogic.pconjunction post f1) excep_post

let conjunction_excep_convert excep_post f1 =
  ClassMap.map (fun post -> Rlogic.conj_convert post f1) excep_post

let convert_excep = ClassMap.map Rlogic.convert

let disjunction_excep excep_post1 excep_post2 =
  let newClassMap = ref ClassMap.empty in 
  let _ = ClassMap.iter 
      (fun key post -> 
	newClassMap := 
	  ClassMap.add 
	    key 
	    (try Plogic.mkOr(post,(ClassMap.find key excep_post2))
	    with Not_found -> post)
	    !newClassMap 
      ) 
    excep_post1 in
  let _ = ClassMap.iter
      (fun key post -> 
	if ClassMap.mem key excep_post1 then () 
	else newClassMap := ClassMap.add key post !newClassMap)
      excep_post2
  in !newClassMap

(*type spec = 
    { pre : representative Plogic.pform;
      post : representative Plogic.pform;
      excep : excep_post }
*)

let spec_conjunction spec1 spec2 =
  let var = Arg_var(Vars.freshe()) in
  let zero = Arg_string("**first**") in
  let one = Arg_string("**second**") in
  let eq = mkEQ(var,zero) in 
  let neq = mkEQ(var,one) in       
  match spec1,spec2 with 
    {pre=pre1; post=post1; excep=excep1},
    {pre=pre2; post=post2; excep=excep2} ->
      {pre= Plogic.mkOr ((Plogic.pconjunction pre1 eq),(Plogic.pconjunction pre2 neq));
       post= Plogic.mkOr ((Plogic.pconjunction post1 eq),(Plogic.pconjunction post2 neq));
       excep = disjunction_excep (conjunction_excep excep1 eq) (conjunction_excep excep2 neq)
     }

(*      
type methodspec =
      Dynamic of method_signature_short * (spec list)
  |   Static of method_signature_short * (spec list)

type methodspecs =
    methodspec list


type apf_define = (string * var * representative fldlist * representative Plogic.pform * bool)

type apf_defines = apf_define list

type class_spec = (class_name * apf_defines * methodspecs)

type spec_file = class_spec list 
*)


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

(* Specs to verification  *)



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
  let (classname,apf,specs) = cs in 
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
	| Global_types.Static (ms,spec) -> 
	    (match ms with 
	      (a,b,c) -> 
		(addMSpecs (cn,a,b,c) (spec_list_to_spec spec) smmap,dmmap)
	    )
    ) 
    (smmap,dmmap) specs 
(*
let class_spec_to_ms cs (smmap,dmmap) =
  let (classname,apf,specs) = cs in 
  List.fold_left 
    (fun (smmap,dmmap) pre_spec
      -> 
	match pre_spec with 
	  Dynamic (ms,spec) -> 
	    (match ms with 
	      Method_signature(cn,a,b,c) -> 
		if(Pprinter.class_name2str cn = Pprinter.class_name2str classname) 
		then (smmap,addMSpecs (cn,a,b,c) (spec_list_to_spec spec) dmmap)
		else (Printf.printf "Defines method for %s in %s.\n" (Pprinter.class_name2str cn) (Pprinter.class_name2str classname)   ;raise Class_defines_external_spec  )
	    | Field_signature _ -> assert false )
	| Static (ms,spec) -> 
	    (match ms with 
	      Method_signature(cn,a,b,c) -> 
		if(Pprinter.class_name2str cn = Pprinter.class_name2str classname) 
		then (addMSpecs (cn,a,b,c) (spec_list_to_spec spec) smmap,dmmap)
		else (Printf.printf "Defines method for %s in %s.\n" (Pprinter.class_name2str cn) (Pprinter.class_name2str classname)   ;raise Class_defines_external_spec  )
	    | Field_signature _ -> assert false )
    ) 
    (smmap,dmmap) specs 
*)

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


let dynamic_to_static apfmap cn spec = 
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

let fix_gaps (smmap,dmmap) apfmap =
  let dmmapr = ref dmmap in 
  let smmapr = ref smmap in 
  let _ = MethodMap.iter 
      (fun key spec -> 
	if MethodMap.mem key (!dmmapr) then () else dmmapr := MethodMap.add key (static_to_dynamic spec) (!dmmapr)
      ) smmap in
  let _ = MethodMap.iter 
      (fun (cn,a,b,c) spec -> 
	if MethodMap.mem (cn,a,b,c) (!smmapr) then () 
	else smmapr := MethodMap.add (cn,a,b,c) (dynamic_to_static apfmap (Pprinter.class_name2str cn) spec) (!smmapr);
	dmmapr := MethodMap.add (cn,a,b,c) (filter_dollar_spec spec) !dmmapr
      ) dmmap in
  (!smmapr,!dmmapr)


let spec_file_to_method_specs sf apfmap =
  let rec sf_2_ms_inner sf (pairmmap) = 
    match sf with 
      [] -> pairmmap
    | cs::sf -> sf_2_ms_inner sf (class_spec_to_ms cs pairmmap)
  in fix_gaps (sf_2_ms_inner sf (emptyMSpecs,emptyMSpecs)) apfmap



let spec_file_to_classapfmap logic sf =
  let rec add_globals sf logic = 
    match sf with
      (classname,apf,specs)::sf -> 
	let logic = add_apf_to_logic logic (List.filter (fun (a,b,x,y,w) -> w) apf) (Pprinter.class_name2str classname) in 
	add_globals sf logic
    | [] -> logic in
  let logic = add_globals sf logic in
  let rec sf2classapfm sf  apfmap = 
  match sf with
    [] -> apfmap
  | (classname,apf,specs)::sf -> 
      let logic = add_apf_to_logic logic apf (Pprinter.class_name2str classname) in 
      sf2classapfm sf   (ClassMap.add classname logic  apfmap)
  in (sf2classapfm sf ClassMap.empty, logic)



(***************************************
   Refinement type stuff 
 ***************************************)


(* 
   { e1 : f1} , ... , {en :  fn}   (excep1)  
   ===>
   { e1' : f1', ... , {em' : fm'}  (excep2)
iff
forall ei :fi. exists ej' : fj'.  ei=ej' /\ fi==>fj'
*)
exception Check_fails

let implication_excep logic excep1 excep2 = 
  try 
    ClassMap.iter (
    fun exname form -> 
      if Prover.check_implication logic form (ClassMap.find exname excep2) 
      then ()
      else raise Check_fails
   ) excep1; true
  with check_fails -> false

let sub_spec  sub spec =
  match spec with 
    {pre=pre; post=post; excep=excep} ->
      {pre=subst_pform sub pre;
       post=subst_pform sub post;
	excep=ClassMap.map (subst_pform sub) excep;}
      
let ev_spec spec = 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let ev = ev_form spec_pre VarSet.empty in 
      let ev = ev_form spec_post ev in 
      let ev = ClassMap.fold (fun key ex vs -> ev_form ex vs) spec_excep ev in 
      ev

let ev_spec_pre spec = 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let ev = ev_form spec_pre VarSet.empty in 
      ev

let jsr logic (pre : Rlogic.ts_form) (spec : spec)  : (Rlogic.ts_form  list * ts_excep_post list) option  = 
  let ev = ev_spec spec in 
  let subst = subst_kill_vars_to_fresh_exist ev in 
  let spec = sub_spec subst spec in 
  match spec with
    {pre=spec_pre; post=spec_post; excep =spec_excep} -> 
      let frame_list = Prover.check_implication_frame logic pre (Rlogic.convert spec_pre) in 
      if frame_list = [] then 
	None
      else
	let res = List.map (fun post -> (*Prover.tidy_one*) (Rlogic.conj_convert spec_post post)) frame_list in 
	let excep_res = List.map (conjunction_excep_convert spec_excep) frame_list in 
	List.iter (fun (ts,_) -> vs_iter (kill_var ts) ev) res;
	Some (res,excep_res)

let logical_vars_to_prog spec2 = 
  let ev = ev_spec_pre spec2 in 
  let sub = subst_kill_vars_to_fresh_prog ev in 
  sub_spec sub spec2 

(*  spec2={P}{Q} =[extra]=> spec1  
 
   {P*extra}{Q} ===> spec1
*)
let refinement_extra (logic : logic) (spec1 : spec) (spec2 : spec) (extra : representative Plogic.pform): bool =
  let spec2 = logical_vars_to_prog spec2 in 
  match spec2 with
    {pre=pre; post=post; excep=excep} ->
      match jsr logic (Rlogic.convert (extra&&&pre)) spec1 with 
	None -> false
      | Some (newposts, newexcep_posts) ->
	  let res = List.for_all (fun newpost -> Prover.check_implication logic newpost (Rlogic.convert post)) newposts in 
	  let res2 = List.for_all (fun newexcep_post -> implication_excep logic newexcep_post (convert_excep excep)) newexcep_posts in 
	  (res&&res2)


(*  spec2 ==> spec1 
That is
   spec2
   -----
     :
   ----- 
   spec1  
*)
let refinement (logic : logic) (spec1 : spec) (spec2 : spec) : bool =
    refinement_extra logic spec1 spec2 [] 


let refinement_this (logic : logic) (spec1 : spec) (spec2 : spec) (cname : class_name): bool =
    refinement_extra logic spec1 spec2 (objtype this_var (Pprinter.class_name2str cname))


