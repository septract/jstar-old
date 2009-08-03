(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Global_types
open Specification
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

let verify_class 
    jimple_file
    static_method_specs 
    dynamic_method_specs 
    apfmap 
    defaultlogic 
    abslogic = 
  let Jparsetree.JFile(_,_,class_name,clpar_opt,implements_opt,_) = jimple_file in
(* Find logic for this class *)
  let logic = try ClassMap.find class_name apfmap with Not_found -> defaultlogic in
(* call symbolic execution for all methods of this class *)
  let _ = Symexec.compute_fixed_point jimple_file apfmap logic abslogic static_method_specs dynamic_method_specs in 
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
      if refinement_this logic my_sta_spec my_dyn_spec (class_name) then 	
	(good();if Config.symb_debug() then Printf.printf "\n\nDynamic spec is consistent with static for %s!\n" (Pprinter.name2str mname); reset())
      else 
	(warning();Printf.printf "\n\nDynamic spec is not consistent with static for %s!\n" (Pprinter.name2str mname);reset()(*; 
         assert false*));
      (* Check BS *)
      if Jparsetree.constructor mname then () else
      ((match clpar_opt with
	Some clpar -> 
	  (try 
	    let par_dyn_spec = MethodMap.find (clpar,rtype,mname,params) dynamic_method_specs in	 
	    if refinement logic my_dyn_spec par_dyn_spec  then 
	      (good();if Config.symb_debug() then Printf.printf "\n\nBehavioural subtyping succeeds for %s in %s!\n"
		(Pprinter.name2str mname) 
		(Pprinter.class_name2str class_name); reset())
	    else 
	      (warning();Printf.printf "\n\nBehavioural subtyping fails for %s in %s!\n"
		(Pprinter.name2str mname) 
		(Pprinter.class_name2str class_name); reset();
	      (*assert false;*))
	  with Not_found -> ());
      (match implements_opt with
	Some interpars -> 
	  List.iter (fun interpar -> 
	    (try 
	    let par_dyn_spec = MethodMap.find (interpar,rtype,mname,params) dynamic_method_specs in	 
	    if refinement logic my_dyn_spec par_dyn_spec  then 
	      (if Config.symb_debug() then Printf.printf "\n\nBehavioural subtyping succeeds for %s in %s!\n" 
		(Pprinter.name2str mname) 
		(Pprinter.class_name2str class_name))
	    else 
	      (Printf.printf "\n\nBehavioural subtyping fails for %s in %s!\n" 
		(Pprinter.name2str mname) 
		(Pprinter.class_name2str class_name);
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
