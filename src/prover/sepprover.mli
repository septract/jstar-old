(********************************************************
   This file is part of jStar 
	src/prover/sepprover.mli
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
open Psyntax



    type inner_form 
    val inner_truth : inner_form 
    val convert : form -> inner_form option
    val conjoin : form -> inner_form -> inner_form
    val conjoin_inner : inner_form -> inner_form -> inner_form
    val kill_var : var -> inner_form -> inner_form
    val kill_all_exists_names : inner_form -> inner_form
    val update_var_to : var -> term -> inner_form -> inner_form
    val form_clone : inner_form -> inner_form
    val form_clone_abs : inner_form -> inner_form
    val string_inner_form : Format.formatter -> inner_form -> unit 
    
(*
    type logic 
    type sequent = form * form * form
    type rewrite_rule = {
      op : string;
      arguments : term list;
      new_term : term;
      rule_name : string;
    }
    type sequent_rule = {
      conclusion : sequent;
      premises : sequent list list;
      name : string;
      without : form;
    }
    val empty_logic : logic
    val add_rewrite_rule : rewrite_rule -> logic -> logic
    val add_sequent_rule : sequent_rule -> logic -> logic
*)
    val implies_inner : logic -> inner_form -> inner_form -> bool
    val implies : logic -> inner_form -> form -> bool
    val implies_opt : logic -> inner_form option -> form -> bool
    val inconsistent : logic -> inner_form -> bool
    val inconsistent_opt : logic -> inner_form option -> bool
    val frame : logic -> inner_form -> form -> inner_form list option
    val frame_opt : logic -> inner_form option -> form -> inner_form list option
    val frame_inner : logic -> inner_form -> inner_form -> inner_form list option
    val abs : logic -> inner_form -> inner_form list
    val abs_opt : logic -> inner_form option -> inner_form list
    val abduction_opt : logic -> inner_form option -> form -> inner_form list option
    val pprint_proof : out_channel -> unit
    val pprint_counter_example : Format.formatter -> unit -> unit 
    val print_counter_example : unit -> unit 
    val string_of_proof : unit -> string 
    val implies_list : inner_form list -> form -> bool 
