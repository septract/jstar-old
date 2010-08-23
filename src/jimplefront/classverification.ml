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
		if Sepprover.implies_opt logic_with_where_pred_defs (Sepprover.convert antecedent) consequent then
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
			if Sepprover.implies_opt logic (Sepprover.convert (Psyntax.pconjunction conjunct antecedent)) consequent then
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
				let c = Sepprover.convert p_antecedent in
				let d = p_consequent in
				if Sepprover.implies_opt logic c d then
					(good(); if Config.symb_debug() then Printf.printf "\n\nParent consistency verification of axiom %s succeeded w.r.t. %s!\n" name parent_name; reset();)
				else
					let a = antecedent in
					let b = Sepprover.convert consequent in
					if Sepprover.implies_opt logic c a && Sepprover.implies_opt logic b d then
						(good(); if Config.symb_debug() then Printf.printf "\n\nParent consistency verification of axiom %s succeeded w.r.t. %s!\n" name parent_name; reset();)
					else
						(warning(); if Config.symb_debug() then Printf.printf "\n\nParent consistency verification of axiom %s failed w.r.t. %s!\n" name parent_name; reset();)
			with Not_found -> ()
		) parents
	) implications

	
let verify_methods
		(jimple_file : Jimple_global_types.jimple_file)
		(static_method_specs : Javaspecs.methodSpecs)
		(dynamic_method_specs : Javaspecs.methodSpecs)
		(logic : logic)
		(abslogic : logic) =
	let Jimple_global_types.JFile(_,_,class_name,_,_,_) = jimple_file in
	let parents = parent_classes_and_interfaces jimple_file in
	let static_specs = MethodMap.fold (fun (cn,a,b,c) (spec,pos) list -> if cn=class_name then ((cn,a,b,c),(spec,pos))::list else list) static_method_specs [] in
	(* Body verification - call symbolic execution for all methods in the jimple file *)
		let _ = Translatejimple.compute_fixed_point jimple_file logic abslogic static_method_specs dynamic_method_specs in
	(* Dynamic dispatch *)
		let _ = if is_class_abstract jimple_file || is_interface jimple_file then
							()
						else
							List.iter (fun (msig,(static_spec, static_pos)) ->
								try
									let _,_,mname,_ = msig in
                                    match (MethodMap.find msig dynamic_method_specs) with
                                       	| (dynamic_spec, dynamic_spec_pos) ->
									      	if refinement_this logic static_spec dynamic_spec class_name then
										     	(good();if Config.symb_debug() then Printf.printf "\n\nDynamic spec is consistent with static for %s!\n" (Pprinter.name2str mname); reset())
									      	else
										    	(let error_text = Printf.sprintf "Dynamic spec is not consistent with static for %s" (Pprinter.name2str mname) in
                                                warning();
                                                Printf.printf "\n\n%s!\n" error_text; 
                                                Printing.eclipse_print_spec dynamic_spec_pos error_text; 
                                                reset())
								with Not_found -> assert false
							) static_specs
		in
	(* Behavioural subtyping of non-constructor methods *)
		let dynamic_specs = MethodMap.fold (fun (cn,a,b,c) (spec,pos) list -> if cn=class_name && not (Jparsetree.constructor b) then ((cn,a,b,c),(spec,pos))::list else list) dynamic_method_specs [] in
		let _ = List.iter (fun ((cn,a,mname,c),(dynamic_spec,dynamic_spec_pos)) ->
			List.iter (fun parent ->
				try
                	match (MethodMap.find (parent,a,mname,c) dynamic_method_specs) with
                    	| (parent_dynamic_spec, parent_dynamic_spec_pos) ->
					      	(*let _ = Printf.printf "\n\nMy spec: %s" ((Debug.toString Pprinter_core.spec2str) dynamic_spec) in
					      	let _ = Printf.printf "\n\nParent spec: %s" ((Debug.toString Pprinter_core.spec2str) parent_dynamic_spec) in*)
					      	if refinement logic dynamic_spec parent_dynamic_spec then
						     	(good();if Config.symb_debug() then Printf.printf "\n\nBehavioural subtyping succeeds for %s in %s w.r.t. %s!\n"
						     	(Pprinter.name2str mname) 
						     	(Pprinter.class_name2str class_name)
						     	(Pprinter.class_name2str parent); reset())
				          	else 
				  	         	(warning();
                             	let error_text = Printf.sprintf "Behavioural subtyping fails for %s in %s w.r.t. %s" 
                                  (Pprinter.name2str mname) 
						          (Pprinter.class_name2str class_name)
						          (Pprinter.class_name2str parent) in
                             	Printf.printf "\n\n%s!\n" error_text;
                             	Printing.eclipse_print_spec dynamic_spec_pos error_text;
                             	reset())
				with Not_found -> ()
			) parents
		) dynamic_specs in
	(* Inheritance *)
		let mdl =  Methdec.make_methdecs_of_list class_name (Methdec.get_list_methods jimple_file) in
		let sigs_of_methods_with_bodies = List.fold_left (fun list m -> if Methdec.has_body m then (class_name,m.ret_type,m.name_m,m.params)::list else list) [] mdl in 
		let static_specs_of_methods_without_bodies = List.filter (fun (msig,_) -> not (List.mem msig sigs_of_methods_with_bodies)) static_specs in
		let _ = List.iter (fun ((_,a,mname,c),(static_spec, static_pos)) ->
			(* stephan mult inh *) (* In the single inheritance case, a lookup can be made for the static spec in the single parent class, resulting in parent_static_specs being [spec] if spec was found, and [] otherwise *)
			let parent_static_specs = List.fold_left (fun list parent ->
               	try
               		match (MethodMap.find (parent,a,mname,c) static_method_specs) with
                    	| (spec, pos) -> spec :: list
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
						(warning();
                         let error_text = Printf.sprintf "Inheritance checking fails for %s" (Pprinter.name2str mname) in
                         if Config.symb_debug() then Printf.printf "\n\n%s!" error_text;
                         Printing.eclipse_print_spec static_pos error_text;  
                         reset())
		) static_specs_of_methods_without_bodies in
	()
