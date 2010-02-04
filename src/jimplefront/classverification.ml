(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Spec_def
open Global_types
open Specification
open Javaspecs
open Support_symex

let warning () =
  Printf.printf "%c[%d;%d;%dm"  (Char.chr 0x1B ) 5  (1 + 30) (0 + 40)

let good () =
  Printf.printf "%c[%d;%d;%dm"  (Char.chr 0x1B ) 1  (2 + 30) (0 + 40)

let reset () =
  Printf.printf "%c[%d;%d;%dm" (Char.chr 0x1B) 0 (7 + 30) (0 + 40)

type methodType = 
    Overridden
  | Inherited
  | New


let method_type msig : methodType = New  (* do something more here *)

let method_set_for_class  classname jfile  =
  let mdl =  Methdec.make_methdecs_of_list classname (Methdec.get_list_methods jfile) in
  let msigs = List.map (fun m -> Methdec.get_msig m classname) mdl in 
  msigs

let is_class_abstract jimple_file =
	let Jimple_global_types.JFile(modifiers,_,_,_,_,_) = jimple_file in
	List.mem Jparsetree.Abstract modifiers
	
let is_interface jimple_file =
	match jimple_file with
		| Jimple_global_types.JFile(_,Jparsetree.InterfaceFile,_,_,_,_) -> true
		| _ -> false

let verify_exports_implications implications logic_with_where_pred_defs =
	List.iter (fun implication ->
		let name,antecedent,consequent = implication in
		if Prover.check_implication logic_with_where_pred_defs (Rlogic.convert antecedent) (Rlogic.convert consequent) then
			(good(); if Config.symb_debug() then Printf.printf "\n\nVerification of exported implication %s succeeded!\n" name; reset();)
		else
			(warning(); if Config.symb_debug() then Printf.printf "\n\nVerification of exported implication %s failed!\n" name; reset();)
	) implications
	
let verify_axioms_implications class_name jimple_file implications logic =
	let abstract_class_or_interface = is_class_abstract jimple_file || is_interface jimple_file in
	let conjunct = Jlogic.mk_type (Pterm.Arg_var Support_syntax.this_var) class_name in 
	List.iter (fun implication ->
		let name,antecedent,consequent = implication in
		(* We first tackle the Implication proof obligation if the class is not abstract or an interface. *)
		if abstract_class_or_interface then
			()
		else
			if Prover.check_implication logic (Rlogic.convert (Plogic.pconjunction conjunct antecedent)) (Rlogic.convert consequent) then
				(good(); if Config.symb_debug() then Printf.printf "\n\nImplication verification of axiom %s succeeded!\n" name; reset();)
			else
				(warning(); if Config.symb_debug() then Printf.printf "\n\nImplication verification of axiom %s failed!\n" name; reset();)
		;
		(* Then we tackle the Parent consistency proof obligation *)
		()
	) implications

let verify_class 
    jimple_file
    static_method_specs 
    dynamic_method_specs 
    logic 
    abslogic = 
  let Jimple_global_types.JFile(modifiers,_,class_name,clpar_opt,implements_opt,_) = jimple_file in
	let abstract_class_or_interface = is_class_abstract jimple_file || is_interface jimple_file in
(* call symbolic execution for all methods of this class *)
  let _ = Translatejimple.compute_fixed_point jimple_file logic abslogic static_method_specs dynamic_method_specs in 
(* Find method set for this class *)
  let mset = method_set_for_class class_name jimple_file in 
(* For each method: *)
  List.iter 
    (fun msig ->
      let (cl,rtype,mname,params)  =  msig in
(*      assert cl=class_name;*)
      let my_sta_spec = try MethodMap.find msig static_method_specs with Not_found -> assert false in
      let my_dyn_spec = 
	try MethodMap.find msig dynamic_method_specs 
	with Not_found -> Printf.printf "\n\n Using static spec for %s" (Pprinter.name2str mname) ; my_sta_spec 
      in
			(* Check Dynamic Dispatch only if the class is not abstract or an interface *)
			if abstract_class_or_interface then
				()
			else
	      if refinement_this logic my_sta_spec my_dyn_spec (class_name) then 	
					(good();if Config.symb_debug() then Printf.printf "\n\nDynamic spec is consistent with static for %s!\n" (Pprinter.name2str mname); reset())
	      else 
					(warning();Printf.printf "\n\nDynamic spec is not consistent with static for %s!\n" (Pprinter.name2str mname);reset()(*; 
	         assert false*));
      (* Check BS *)
      if Jparsetree.constructor mname then () else
      ((match clpar_opt with
      |	None -> assert false
      |	Some clpars -> 
					List.iter (fun clpar -> 
				  (try 
				    let par_dyn_spec = MethodMap.find (clpar,rtype,mname,params) dynamic_method_specs in	 
				    if refinement logic my_dyn_spec par_dyn_spec  then 
				      (good();if Config.symb_debug() then Printf.printf "\n\nBehavioural subtyping succeeds for %s in %s w.r.t. %s!\n" 
					(Pprinter.name2str mname) 
					(Pprinter.class_name2str class_name)
					(Pprinter.class_name2str clpar); reset())
				    else 
				      (warning();Printf.printf "\n\nBehavioural subtyping fails for %s in %s w.r.t. %s!\n" 
					(Pprinter.name2str mname) 
					(Pprinter.class_name2str class_name)
					(Pprinter.class_name2str clpar); reset();
				      (*assert false;*))
				  with Not_found -> ()))
				    clpars;
      (match implements_opt with
	Some interpars -> 
	  List.iter (fun interpar -> 
	    (try 
	    let par_dyn_spec = MethodMap.find (interpar,rtype,mname,params) dynamic_method_specs in	 
	    if refinement logic my_dyn_spec par_dyn_spec  then 
	      (if Config.symb_debug() then Printf.printf "\n\nBehavioural subtyping succeeds for %s in %s w.r.t. %s!\n" 
		(Pprinter.name2str mname) 
		(Pprinter.class_name2str class_name)
		(Pprinter.class_name2str interpar))
	    else 
	      (Printf.printf "\n\nBehavioural subtyping fails for %s in %s w.r.t. %s!\n" 
		(Pprinter.name2str mname) 
		(Pprinter.class_name2str class_name)
		(Pprinter.class_name2str interpar);
	      (*assert false;*))
	  with Not_found -> ()))
	    interpars
      | None -> ())));

      match method_type msig with
   (* if new *)
      |	New -> ()
	   (*dino does already*) (* verify static spec against code *)
	    (* verify dynamic spec is implied by static spec *)
   (* if overridden *)
      |	Overridden -> ()
		
   (* if inherited *) 
      |	Inherited -> ()    
	    (* verify static spec is implied by static spec *)
	    (* verify behaviroual subtying *)
	    (* verify static spec is a refinement of parent's *)
    )
    mset 
