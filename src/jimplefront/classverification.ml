(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Spec_def
open Psyntax
open Specification
open Javaspecs
open Support_symex
open Jimple_global_types
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
	List.iter (fun implication ->
		let name,antecedent,consequent = implication in
		if Prover.check_implication logic_with_where_pred_defs (Rlogic.convert antecedent) (Rlogic.convert consequent) then
			(good(); if Config.symb_debug() then Printf.printf "\n\nVerification of exported implication %s succeeded!\n" name; reset();)
		else
			(warning(); if Config.symb_debug() then Printf.printf "\n\nVerification of exported implication %s failed!\n" name; reset();)
	) implications

(* Check both proof obligations (Implication and Parent consistency) for each axiom in 'implications'. *)
let verify_axioms_implications class_name jimple_file implications axiom_map logic =
	let abstract_class_or_interface = is_class_abstract jimple_file || is_interface jimple_file in
	let parents = parent_classes_and_interfaces jimple_file in
	let conjunct = Jlogic.mk_type (Arg_var Support_syntax.this_var) class_name in 
	List.iter (fun implication ->
		let name,antecedent,consequent = implication in
		(* We first tackle the Implication proof obligation if the class is not abstract or an interface. *)
		if abstract_class_or_interface then
			()
		else
			if Prover.check_implication logic (Rlogic.convert (Psyntax.pconjunction conjunct antecedent)) (Rlogic.convert consequent) then
				(good(); if Config.symb_debug() then Printf.printf "\n\nImplication verification of axiom %s succeeded!\n" name; reset();)
			else
				(warning(); if Config.symb_debug() then Printf.printf "\n\nImplication verification of axiom %s failed!\n" name; reset();)
		;
		(* Then we tackle the Parent consistency proof obligation *)
		List.iter (fun parent ->
			let parent_name = (Pprinter.class_name2str parent) in
			try
				let p_antecedent,p_consequent = AxiomMap.find (parent,name) axiom_map in
				(* We must verify (antecedent=>consequent) => (p_antecedent=>p_consequent) *)
				(* Since (a=>b) => (c=>d) is equivalent to *)
				(* (c=>d) \/ [(c=>a) /\ (b=>d)], we do the following: *)
				let c = Rlogic.convert p_antecedent in
				let d = Rlogic.convert p_consequent in
				if Prover.check_implication logic c d then
					(good(); if Config.symb_debug() then Printf.printf "\n\nParent consistency verification of axiom %s succeeded w.r.t. %s!\n" name parent_name; reset();)
				else
					let a = Rlogic.convert antecedent in
					let b = Rlogic.convert consequent in
					if Prover.check_implication logic c a && Prover.check_implication logic b d then
						(good(); if Config.symb_debug() then Printf.printf "\n\nParent consistency verification of axiom %s succeeded w.r.t. %s!\n" name parent_name; reset();)
					else
						(warning(); if Config.symb_debug() then Printf.printf "\n\nParent consistency verification of axiom %s failed w.r.t. %s!\n" name parent_name; reset();)
			with Not_found -> ()
		) parents
	) implications
	
let verify_methods
		jimple_file
		static_method_specs
		dynamic_method_specs
		logic
		abslogic =
	let Jimple_global_types.JFile(_,_,class_name,_,_,_) = jimple_file in
	let parents = parent_classes_and_interfaces jimple_file in
	let static_specs = MethodMap.fold (fun (cn,a,b,c) spec list -> if cn=class_name then ((cn,a,b,c),spec)::list else list) static_method_specs [] in
	(* Body verification - call symbolic execution for all methods in the jimple file *)
		let _ = Translatejimple.compute_fixed_point jimple_file logic abslogic static_method_specs dynamic_method_specs in
	(* Dynamic dispatch *)
		let _ = if is_class_abstract jimple_file || is_interface jimple_file then
							()
						else
							List.iter (fun (msig,static_spec) ->
								try
									let _,_,mname,_ = msig in
									let dynamic_spec = MethodMap.find msig dynamic_method_specs in
									if refinement_this logic static_spec dynamic_spec class_name then
										(good();if Config.symb_debug() then Printf.printf "\n\nDynamic spec is consistent with static for %s!\n" (Pprinter.name2str mname); reset())
									else
										(warning();Printf.printf "\n\nDynamic spec is not consistent with static for %s!\n" (Pprinter.name2str mname);reset())
								with Not_found -> assert false
							) static_specs
		in
	(* Behavioural subtyping of non-constructor methods *)
		let dynamic_specs = MethodMap.fold (fun (cn,a,b,c) spec list -> if cn=class_name && not (Jparsetree.constructor b) then ((cn,a,b,c),spec)::list else list) dynamic_method_specs [] in
		let _ = List.iter (fun ((cn,a,mname,c),dynamic_spec) ->
			List.iter (fun parent ->
				try
					let parent_dynamic_spec = MethodMap.find (parent,a,mname,c) dynamic_method_specs in
					(*let _ = Printf.printf "\n\nMy spec: %s" ((Debug.toString Pprinter_core.spec2str) dynamic_spec) in
					let _ = Printf.printf "\n\nParent spec: %s" ((Debug.toString Pprinter_core.spec2str) parent_dynamic_spec) in*)
					if refinement logic dynamic_spec parent_dynamic_spec then
						(good();if Config.symb_debug() then Printf.printf "\n\nBehavioural subtyping succeeds for %s in %s w.r.t. %s!\n"
						(Pprinter.name2str mname) 
						(Pprinter.class_name2str class_name)
						(Pprinter.class_name2str parent); reset())
				  else 
				  	(warning();Printf.printf "\n\nBehavioural subtyping fails for %s in %s w.r.t. %s!\n" 
						(Pprinter.name2str mname) 
						(Pprinter.class_name2str class_name)
						(Pprinter.class_name2str parent); reset())
				with Not_found -> ()
			) parents
		) dynamic_specs in
	(* Inheritance *)
		let mdl =  Methdec.make_methdecs_of_list class_name (Methdec.get_list_methods jimple_file) in
		let sigs_of_methods_with_bodies = List.fold_left (fun list m -> if Methdec.has_body m then (class_name,m.ret_type,m.name_m,m.params)::list else list) [] mdl in 
		let static_specs_of_methods_without_bodies = List.filter (fun (msig,_) -> not (List.mem msig sigs_of_methods_with_bodies)) static_specs in
		let _ = List.iter (fun ((_,a,mname,c),static_spec) ->
			(* stephan mult inh *) (* In the single inheritance case, a lookup can be made for the static spec in the single parent class, resulting in parent_static_specs being [spec] if spec was found, and [] otherwise *)
			let parent_static_specs = List.fold_left (fun list parent ->
				try
					MethodMap.find (parent,a,mname,c) static_method_specs :: list
				with Not_found -> list
			) [] parents in
			match parent_static_specs with
				| [] -> (warning();if Config.symb_debug() then Printf.printf "\n\nMethod %s has a static spec and no body, and no parent appears to list a static spec for it. Maybe it is abstract and not declared as such in the spec file." (Pprinter.name2str mname);reset())
				| _ ->
					let ancestor_static_spec = spec_list_to_spec parent_static_specs in
					(*let _ = Printf.printf "\n\nMy spec: %s" ((Debug.toString Pprinter_core.spec2str) static_spec) in
					let _ = Printf.printf "\n\nAncestor spec: %s" ((Debug.toString Pprinter_core.spec2str) ancestor_static_spec) in*)					
					if refinement logic ancestor_static_spec static_spec then
						(good();if Config.symb_debug() then Printf.printf "\n\nInheritance checking succeeds for %s!" (Pprinter.name2str mname);reset())
					else
						(warning();if Config.symb_debug() then Printf.printf "\n\nInheritance checking fails for %s!" (Pprinter.name2str mname);reset())
		) static_specs_of_methods_without_bodies in
	()
