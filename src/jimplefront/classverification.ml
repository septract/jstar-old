(********************************************************
   This file is part of jStar
        src/jimplefront/classverification.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


open Debug
open Format
open Javaspecs
open Jimple_global_types
open Printing
open Psyntax
open Spec_def
open Specification
open Support_symex
open System

let is_class_abstract jimple_file =
	let Jimple_global_types.JFile(modifiers,_,_,_,_,_) = jimple_file in
	List.mem Jparsetree.Abstract modifiers

let is_interface jimple_file =
	match jimple_file with
		| Jimple_global_types.JFile(_,Jparsetree.InterfaceFile,_,_,_,_) -> true
		| _ -> false

let parent_classes_and_interfaces (jfile : Jimple_global_types.jimple_file) =
	let Jimple_global_types.JFile(_,_,_,parent_classes,parent_interfaces,_) = jfile in
	parent_classes @ parent_interfaces  (* stephan mult inh *)

let verify_exports_implications implications logic_with_where_pred_defs =
  List.iter
    (fun implication ->
      let name,antecedent,consequent = implication in
      let antecedent = Sepprover.convert antecedent in
      if Sepprover.implies_opt logic_with_where_pred_defs antecedent consequent then
        (if log log_exec then printf "@{<g> OK@}: exported implication %s@." name)
      else
        printf "@{<b>NOK@}: exported implication %s@." name)
    implications

(* Check both proof obligations (Implication and Parent consistency) for each axiom in 'implications'. *)
let verify_axioms_implications class_name jimple_file implications axiom_map (logic : logic) =
  let abstract_class_or_interface =
    is_class_abstract jimple_file || is_interface jimple_file in
  let parents = parent_classes_and_interfaces jimple_file in
  let conjunct = Jlogic.mk_type (Arg_var Support_syntax.this_var) class_name in
  List.iter (fun implication ->
      let name,antecedent,consequent = implication in
      (* We first tackle the Implication proof obligation if the class is not abstract or an interface. *)
      if not abstract_class_or_interface then (
        let antecedent =
          Sepprover.convert (Psyntax.pconjunction conjunct antecedent) in
        let m = sprintf "implication verification of axiom %s" name in
        if Sepprover.implies_opt logic antecedent consequent then
          (if log log_logic then printf "@{<g> OK@}: %s@." m)
        else
          printf "@{<b>NOK@}: %s@." m);
      (* Then we tackle the Parent consistency proof obligation *)
      List.iter (fun parent ->
          let parent_name = (Pprinter.class_name2str parent) in
          try
            let p_antecedent,p_consequent =
              AxiomMap.find (parent,name) axiom_map in
            (* We must verify
                 (antecedent=>consequent) => (p_antecedent=>p_consequent)
               which is equivalent to
                 (p_antecedent => p_consequent) \/
                 ((p_antecedent => antecedent) /\ (consequent => p_consequent))
             *)
            let m =
              sprintf "axiom %s consistent with parent %s" name parent_name in
            let p_antecedent = Sepprover.convert p_antecedent in
            let consequent = Sepprover.convert consequent in
            if Sepprover.implies_opt logic p_antecedent p_consequent ||
                (Sepprover.implies_opt logic p_antecedent antecedent &&
                Sepprover.implies_opt logic consequent p_consequent) then
              (if log log_logic then printf "@{<g>OK@}: %s@." m)
            else
              (* Note that P\/Q may be valid even if P and Q are not! *)
              (* TODO(rgrig): Try to not approximate the condition. *)
              printf "@{<b>POSSIBLY NOK@}: %s@." m;
          with Not_found -> () (* TODO(rgrig): Should this print something? *)
      ) parents
  ) implications

let verify_methods
    (jimple_file : Jimple_global_types.jimple_file)
    (static_method_specs : Javaspecs.methodSpecs)
    (dynamic_method_specs : Javaspecs.methodSpecs)
    (logic : logic)
    (abslogic : logic) : unit =
  let Jimple_global_types.JFile(_,_,class_name,_,_,_) = jimple_file in
  let parents = parent_classes_and_interfaces jimple_file in
  let keep_cn = MethodMapH.filter (fun (cn,_,_,_) _ -> cn = class_name) in
  let static_specs = keep_cn static_method_specs in

  (* Body verification - call symbolic execution for all methods in the jimple file *)
  Translatejimple.verify_jimple_file
      jimple_file
      logic
      abslogic
      static_method_specs
      dynamic_method_specs;

  (* Dynamic dispatch *)
  if not (is_class_abstract jimple_file || is_interface jimple_file) then
    let pss msig (ss,_) = (* process static spec *)
      let _,_,mname,_ = msig in
      let ds, dsp = MethodMap.find msig dynamic_method_specs in
      if refinement_this logic ss ds class_name then (
        if log log_exec then
          fprintf logf "Dynamic and static specs of %a are consistent.@."
              Jparsetree.pp_name mname)
      else
        (let et =
          sprintf "Dynamic and static specs of %s disagree."
            (Pprinter.name2str mname) in
        printf "@{<b>WARNING@}: %s@." et; pp_json_location_opt dsp et "") in
    (try MethodMap.iter pss static_specs
    with Not_found -> 
       failwith "Internal error: Couldn't get dynamic specs for some method.");

  (* Behavioural subtyping of non-constructor methods *)
  let dynamic_specs =
    MethodMapH.filter
        (fun (_,_,mn,_) _ -> not (Jparsetree.constructor mn))
        (keep_cn dynamic_method_specs) in
  let pds (cn,a,mn,c) (ds,_) = (* process dynamic spec *)
    let pp p = (* process parent *)
      try
        let ds',dsp' = MethodMap.find (p,a,mn,c) dynamic_method_specs in
        if refinement logic ds ds' then (
          if log log_exec then
            fprintf logf "OK: %a#%a <: %a#%a@."
                Jparsetree.pp_class_name class_name
                Jparsetree.pp_name mn
                Jparsetree.pp_class_name p
                Jparsetree.pp_name mn)
        else
          let et = sprintf "%s#%s not <: %s#%s"
            (Pprinter.class_name2str class_name) (Pprinter.name2str mn)
            (Pprinter.class_name2str p) (Pprinter.name2str mn) in
          (printf "@{<b>WARNING@}: %s@." et; pp_json_location_opt dsp' et "")
      with Not_found -> () (* TODO(rgrig): Really ignore this? *) in
    List.iter pp parents in
  MethodMap.iter pds dynamic_specs;

	(* Inheritance *)
  let ms = (* methods *)
    Methdec.make_methdecs_of_list
        class_name
        (Methdec.get_list_methods jimple_file) in
  let ms = List.filter Methdec.has_body ms in
  let sigs = (* ... for methods with bodies *)
    List.fold_left
        (fun a m ->
            MethodSet.add (class_name, m.ret_type, m.name_m, m.params) a)
        MethodSet.empty
        ms in
  let sss =
    MethodMapH.filter (fun s _ -> not (MethodSet.mem s sigs)) static_specs in
	MethodMap.iter (fun (_,a,mname,c) (static_spec, static_pos) ->
      (* stephan mult inh *) (* In the single inheritance case, a lookup can be made for the static spec in the single parent class, resulting in parent_static_specs being [spec] if spec was found, and [] otherwise *)
      let parent_static_specs = List.fold_left (fun list parent ->
        try 
          match (MethodMap.find (parent,a,mname,c) static_method_specs) with
          | (ss,_) -> ss :: list
        with Not_found -> list
      ) [] parents in
      match parent_static_specs with
        | [] ->
            printf
                "@[<4>@{<b>WARNING@}: Should method %a be declared abstract \
                    in the spec file?@ It has a static spec,@ no body,@ and \
                    no parent lists a static spec for it.@\n\
                    @{<b>(end of warning)@}@."
                Jparsetree.pp_name mname
        | pss ->
          let ancestor_static_spec = spec_list_to_spec pss in
          if Config.symb_debug () then (
            let et =
              sprintf "Inheritance check for %s." (Pprinter.name2str mname) in
            if refinement logic ancestor_static_spec static_spec then
              printf "@{<g> OK@}"
            else
              (printf "@{<b>NOK@}"; pp_json_location_opt static_pos et "");
            printf "%s@." et))
      sss
