(********************************************************
   This file is part of jStar
        src/prover/sepprover.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(*F#
namespace Microsoft.Research.Vcc2
F#*)

open Debug
open Psyntax


    (*****************************************
       Internal formula operations
     *****************************************)

    type inner_form = Clogic.F.ts_formula
    
    type inner_form_af = Clogic.AF.ts_formula

    let lift_inner_form inner_form = 
      let ts,form = Clogic.break_ts_form inner_form in
      Clogic.mk_ts_form_af ts form Clogic.empty

    let inner_form_af_to_form inner_form_af =
      let ts,form,af = Clogic.break_ts_form_af inner_form_af in
      Clogic.mk_ts_form ts form

    let inner_form_af_to_af inner_form_af =
      let ts,form,af = Clogic.break_ts_form_af inner_form_af in
      Clogic.mk_ts_form ts af
      
    let inner_truth = 
      Clogic.mk_ts_form (Cterm.new_ts ()) Clogic.truth
    
    let inner_falsum =
      let form,ts = Clogic.convert_sf false (Cterm.new_ts ()) Clogic.false_sform in
      Clogic.mk_ts_form ts form

    let convert : form -> inner_form option  
      = fun form -> 
        try Some (Clogic.convert_with_eqs false form)
        with Contradiction -> None 

    let conjoin : form -> inner_form -> inner_form 
      = fun form inner_form -> Clogic.conjoin false inner_form (Clogic.convert_to_inner form)

    let conjoin_inner : inner_form -> inner_form -> inner_form
      = fun if1 if2 -> Clogic.conjoin false if1 (Clogic.make_syntactic if2)

    (* Takes inner_form_af and conjoins frame with form, and antiframe with inner_form *)
    let conjoin_af : inner_form_af -> form -> inner_form -> inner_form_af
      = fun inner_form_af form inner_form ->
        Clogic.conjoin_af false inner_form_af (Clogic.convert_to_inner form) (Clogic.make_syntactic inner_form)

    (* Takes inner_form_af and conjoins frame with 1st inner_form, and antiframe with 2nd inner_form *)
    let conjoin_inner_af : inner_form_af -> inner_form -> inner_form -> inner_form_af
      = fun inner_form_af if1 if2 ->
        Clogic.conjoin_af false inner_form_af (Clogic.make_syntactic if1) (Clogic.make_syntactic if2)
        
    (* Takes two inner_forms and creates a inner_form_af with the second inner_form as antiframe *)
    let combine : inner_form -> inner_form -> inner_form_af
      = fun if1 if2 -> Clogic.combine false if1 (Clogic.make_syntactic if2)
    
    let kill_var : var -> inner_form -> inner_form
      = fun v inner_form -> 
        Clogic.kill_var inner_form v

    let kill_var_af : var -> inner_form_af -> inner_form_af
      = fun v inner_form_af ->
        Clogic.kill_var_af inner_form_af v

    let abstract_val : inner_form -> inner_form
      = fun inner_form ->
        let pform = Clogic.ts_form_to_pform inner_form in
        let abs_pform = Plugin_manager.abstract_val pform in
        let abs_inner_form = Clogic.pform_to_ts_form abs_pform in
        abs_inner_form

    let join : inner_form -> inner_form -> inner_form
      = fun if1 if2 ->
        let pf1 = Clogic.ts_form_to_pform if1 in
        let pf2 = Clogic.ts_form_to_pform if2 in
        match Plugin_manager.join pf1 pf2 with
        | [] -> Format.printf "No plugin with join loaded!\n"; inner_truth
        | pf::_ -> Clogic.pform_to_ts_form pf
    
    let meet : inner_form -> inner_form -> inner_form
      = fun if1 if2 ->
        let pf1 = Clogic.ts_form_to_pform if1 in
        let pf2 = Clogic.ts_form_to_pform if2 in
        match Plugin_manager.meet pf1 pf2 with
        | [] -> Format.printf "No plugin with meet loaded!\n"; inner_falsum
        | pf::_ -> Clogic.pform_to_ts_form pf
    
    let widening : inner_form -> inner_form -> inner_form
      = fun if1 if2 ->
        let pf1 = Clogic.ts_form_to_pform if1 in
        let pf2 = Clogic.ts_form_to_pform if2 in
        match Plugin_manager.widening pf1 pf2 with
        | [] -> Format.printf "No plugin with widening loaded!\n"; inner_truth
        | pf::_ -> Clogic.pform_to_ts_form pf   

    let join_over_numeric : inner_form -> inner_form -> form -> 
        (inner_form * inner_form) * (inner_form * inner_form) * form
      = fun if1 if2 pf_add ->
        let split_numerical pform =
          List.partition (fun pf_at -> is_numerical_pform_at pf_at) pform in
        let num_pf1,rest_pf1 = split_numerical (Clogic.ts_form_to_pform if1) in
        let num_pf2,rest_pf2 = split_numerical (Clogic.ts_form_to_pform if2) in
        (* Calculate join over numerical part of the formula *)
        let join =
          match Plugin_manager.join num_pf1 num_pf2 with
          | [] -> Format.printf "No plugin with join loaded!\n%!"; []
          | pf::_ -> pf
        in
        (* Join may expand abstract value of each formula to contain the least common environment
           of the two during which some constraints important for the spatial part may get lost, 
           so we put back in what's missing *)
        let constraints_with_vars pf vars =
          vs_fold (fun var f ->
            f @ (List.filter (fun pa -> contains_subterm_pform_at pa (Vars.string_var var)) pf)) 
            vars []
          in
        let inflate_constraints from_pf in_pf not_in_vs =
          let rec inflate_constraints2 from_pf =
            let pform_eq pf1 pf2 =
              String.compare (string_of string_form pf1) (string_of string_form pf2) = 0 in
            let from_pf_vs = vs_diff (fv_form from_pf) not_in_vs in
            let from_pf_new = constraints_with_vars in_pf from_pf_vs in
            if pform_eq from_pf_new from_pf then from_pf
            else inflate_constraints2 from_pf_new 
          in
          inflate_constraints2 from_pf
        in          
        let join_vars = fv_form join in
        let rest_pf1_vars = fv_form rest_pf1 in
        let rest_pf2_vars = fv_form rest_pf2 in
        let pf1_not_in_vs = vs_union join_vars rest_pf2_vars in
        let pf2_not_in_vs = vs_union join_vars rest_pf1_vars in
        
        let print_vars vs =
          vs_fold (fun var s -> s ^ " " ^ (Vars.string_var var)) vs "" in
        if Config.symb_debug() then
          (Format.printf "\njoin_vars: %s\n%!" (print_vars join_vars);
          Format.printf "\nrest_pf1_vars: %s\n%!" (print_vars rest_pf1_vars);
          Format.printf "\nrest_pf2_vars: %s\n%!" (print_vars rest_pf2_vars);
          Format.printf "\npf1_not_in_vs: %s\n%!" (print_vars pf1_not_in_vs);
          Format.printf "\npf2_not_in_vs: %s\n%!" (print_vars pf2_not_in_vs););
        
        (* First determine missing contraints mentioning vars from the rest *)
        let pf1_missing = constraints_with_vars num_pf1 (vs_diff rest_pf1_vars pf1_not_in_vs) in
        let pf2_missing = constraints_with_vars num_pf2 (vs_diff rest_pf2_vars pf2_not_in_vs) in
        (* Then keep adding numerical constraints until saturation *)
        let pf1_missing = inflate_constraints pf1_missing num_pf1 pf1_not_in_vs in
        let pf2_missing = inflate_constraints pf2_missing num_pf2 pf2_not_in_vs in
        let pf_missing = pf1_missing @ pf2_missing in
        let join = join @ pf_missing @ pf_add in
        if Config.symb_debug() then
          Format.printf "\nAfter adding missing contraints: %a@.\n%!" string_form join;
        (* Conjoin the resulting with the remaining parts of formulae and return all *)
        let join_inner = Clogic.pform_to_ts_form join in
        let rest_inner1 = Clogic.convert_with_eqs false rest_pf1 in
        let rest_inner2 = Clogic.convert_with_eqs false rest_pf2 in
        ((conjoin_inner join_inner rest_inner1, rest_inner1),
        (conjoin_inner join_inner rest_inner2, rest_inner2), pf_missing)

    let update_var_to : var -> term -> inner_form -> inner_form
      = fun v e f -> Clogic.update_var_to f v e

    let update_var_to_af : var -> term -> inner_form_af -> inner_form_af
      = fun v e f -> Clogic.update_var_to_af f v e

    let string_inner_form : Format.formatter -> inner_form -> unit = 
      Clogic.pp_ts_formula

    let string_inner_form_af : Format.formatter -> inner_form_af -> unit =
      Clogic.pp_ts_formula_af

    (******************************************
       Entailment operations
     ******************************************)

    let implies : logic -> inner_form -> form -> bool 
      = fun logic inner_form1 form2 -> Prover.check_implication_pform logic inner_form1 form2

    let implies_opt : logic -> inner_form option -> form -> bool 
      = fun logic inner_form1 form2 -> 
	match inner_form1 with 
	  None -> true 
	| Some inner_form1 -> Prover.check_implication_pform logic inner_form1 form2

    let inconsistent : logic -> inner_form -> bool
      = fun logic inner_form1 -> Prover.check_inconsistency logic inner_form1

    let inconsistent_opt : logic -> inner_form option -> bool
      = fun logic inner_form1 -> 
	match inner_form1 with 
	  None -> true 
	| Some inner_form1 -> Prover.check_inconsistency logic inner_form1

    let frame : logic -> inner_form -> form -> inner_form list option
      = fun logic inner_form1 form2 -> 
	Prover.check_implication_frame_pform logic inner_form1 form2

    let frame_opt : logic -> inner_form option -> form -> inner_form list option
	= fun logic inner_form1 form2 -> 
	  match inner_form1 with 
	    None -> Some []
	  | Some inner_form1 -> 
	      Prover.check_implication_frame_pform logic inner_form1 form2

    let frame_inner (l : logic) (i1 : inner_form) (i2 : inner_form) : inner_form list option = 
      Prover.check_frame l i1 i2

    let abs : logic -> inner_form -> inner_form list 
      = Prover.abs

    let abs_opt : logic -> inner_form option -> inner_form list 
      = fun l form -> match form with None -> [] | Some form -> Prover.abs l form

    let implies_list : inner_form list -> form -> bool 
      = Prover.check_implies_list 

    let abduction_opt (l : logic) (i1 : inner_form option) (f2 : form) : inner_form_af list option = 	
      match i1 with 
        None -> Prover.check_abduction_pform l (Clogic.convert_with_eqs false []) f2
      | Some inner_form -> Prover.check_abduction_pform l inner_form f2 


   let pprint_proof = Prover.pprint_proof
   let pprint_counter_example = Prover.pprint_counter_example   
   let print_counter_example = Prover.print_counter_example
   let get_counter_example = Prover.get_counter_example
   let string_of_proof = Prover.string_of_proof
