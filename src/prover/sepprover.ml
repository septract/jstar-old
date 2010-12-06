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
    
    type inner_form_antiform = Clogic.AF.ts_formula

    let lift_inner_form inner_form = 
      let ts,form = Clogic.break_ts_form inner_form in
      Clogic.mk_ts_form_af ts form Clogic.empty

    let inner_form_antiform_to_form inner_form_af =
      let ts,form,antiform = Clogic.break_ts_form_af inner_form_af in
      Clogic.mk_ts_form ts form

    let inner_form_antiform_to_antiform inner_form_af =
      let ts,form,antiform = Clogic.break_ts_form_af inner_form_af in
      Clogic.mk_ts_form ts antiform
      
    let inner_truth = Clogic.mk_ts_form (Cterm.new_ts ()) Clogic.truth 

    let convert : form -> inner_form option  
      = fun form -> 
        try 
          Some (Clogic.convert_with_eqs false form)
        with Contradiction -> 
          None 

    let conjoin : form -> inner_form -> inner_form 
      = fun form inner_form -> Clogic.conjoin false inner_form (Clogic.convert_to_inner form)

    let conjoin_inner : inner_form -> inner_form -> inner_form
      = fun if1 if2 -> Clogic.conjoin false if1 (Clogic.make_syntactic if2)

    (* Takes inner_from_antiform and conjoins frame with form, and antiframe with inner_form *)
    let conjoin_af : inner_form_antiform -> form -> inner_form -> inner_form_antiform
      = fun inner_form_antiform form inner_form ->
        Clogic.conjoin_af false inner_form_antiform (Clogic.convert_to_inner form) (Clogic.make_syntactic inner_form)
    
    (* Takes two inner_forms and creates a inner_form_antiform with the second inner_form as antiframe *)
    let combine : inner_form -> inner_form -> inner_form_antiform
      = fun if1 if2 -> Clogic.combine false if1 (Clogic.make_syntactic if2)
    
    let kill_var : var -> inner_form -> inner_form
      = fun v inner_form -> 
        Clogic.kill_var inner_form v

    let kill_var_af : var -> inner_form_antiform -> inner_form_antiform
      = fun v inner_form_antiform ->
        Clogic.kill_var_af inner_form_antiform v

    let kill_all_exists_names : inner_form -> inner_form
      = fun inner_form -> inner_form (*assert false  (* TODO. Should do some form of compression of formula *) *)

    let kill_all_exists_names_af : inner_form_antiform -> inner_form_antiform
      = fun inner_form_antiform -> inner_form_antiform (*assert false  (* TODO. Should do some form of compression of formula *) *)

    let update_var_to : var -> term -> inner_form -> inner_form
      = fun v e f -> Clogic.update_var_to f v e

    let update_var_to_af : var -> term -> inner_form_antiform -> inner_form_antiform
      = fun v e f -> Clogic.update_var_to_af f v e

    let string_inner_form : Format.formatter -> inner_form -> unit = 
      Clogic.pp_ts_formula

    let string_inner_form_af : Format.formatter -> inner_form_antiform -> unit =
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

(* TODO: remove
    let implies_inner : logic -> inner_form -> inner_form -> bool 
      = fun logic inner_form1 inner_form2 -> Prover.check_implication logic inner_form1 inner_form2
*)
    let frame : logic -> inner_form -> form -> inner_form list option
      = fun logic inner_form1 form2 -> 
	Prover.check_implication_frame_pform logic inner_form1 form2

    let frame_opt : logic -> inner_form option -> form -> inner_form list option
	= fun logic inner_form1 form2 -> 
	  match inner_form1 with 
	    None -> Some []
	  | Some inner_form1 -> 
	      Prover.check_implication_frame_pform logic inner_form1 form2

    let frame_inner 
         (l : logic)
         (i1 : inner_form)
         (i2 : inner_form)
         : inner_form list option
         = 
	Prover.check_frame l i1 i2

    let abs : logic -> inner_form -> inner_form list 
      = Prover.abs

    let abs_opt : logic -> inner_form option -> inner_form list 
      = fun l form -> match form with None -> [] | Some form -> Prover.abs l form

    let implies_list : inner_form list -> form -> bool 
	= Prover.check_implies_list 

    let abduction_opt (l : logic) (i1 : inner_form option) (f2 : form) : inner_form_antiform list option = 	
      match i1 with 
        None -> Prover.check_abduction_pform l (Clogic.convert_with_eqs false []) f2
      | Some inner_form -> Prover.check_abduction_pform l inner_form f2 


(*

Need to do something better here for integration with multiple SMT provers and such like.

    (******************************************
	  External prover calls
	 ******************************************)
    type out_term = 
    | Fun of string * out_term list
    | PVar of string 
    | EVar of string
    | String of string
    
    type out_form = 
    | EQ of out_term * out_term
    | NEQ of out_term * out_term
    | Pred of string * out_term list
    | Or of out_form * out_form
    | And of out_form * out_form 
    | TT 
    | FF 
 

 
    let rec conv_t interp a  = 
      try let v = Hashtbl.find interp a in v
      with Not_found -> 
      let v = match a with
        | Psyntax.Arg_string n -> String n
        | Psyntax.Arg_op (n,al) -> Fun(n, List.map (conv_t interp) al)
        | Psyntax.Arg_var (Vars.PVar(v,n)) -> PVar (Vars.string_var (Vars.PVar(v,n))) 
        | Psyntax.Arg_var (Vars.EVar(v,n)) -> EVar (Vars.string_var (Vars.EVar(v,n))) 
        | _ -> Printf.printf "Don't know how to convert this term to external use."; unsupported ()
      in Hashtbl.add interp a v; v
      
    let rec conv interp (pl : representative Psyntax.pform) : out_form = 
      let conv_t = conv_t interp in 
      match pl with
        [] -> TT 
      | Psyntax.P_EQ(a1,a2)::pl -> And (EQ(conv_t a1, conv_t a2), conv interp pl) 
      | Psyntax.P_NEQ(a1,a2)::pl -> And (NEQ(conv_t a1, conv_t a2), conv interp pl) 
      | Psyntax.P_PPred(name,al)::pl -> And (Pred(name,List.map conv_t al), conv interp pl) 
      | Psyntax.P_Or(p1,p2)::pl -> And(Or(conv interp p1, conv interp p2), conv interp pl)
      | Psyntax.P_False::pl -> FF
      | _ -> Printf.printf "Don't know how to convert this formula to external use.\n"; unsupported ()

    let add_external_prover : logic -> (out_form -> out_form -> bool) -> logic =
      fun (Logic (x,y,(ep1,ep2))) z -> Logic (x,y,
					      ((fun (p1 : representative Psyntax.pform) 
						  (p2 : representative Psyntax.pform) 
						-> let interp = Hashtbl.create 30 in z (conv interp p1) (conv interp p2))
						,ep2))
 
    let add_external_congruence : logic -> (out_form -> out_term list -> out_term list list) -> logic
	=
      fun (Logic (x,y,(ep1,ep2))) z -> Logic (x,y,
					      (ep1,(fun (p1 : representative Psyntax.pform) 
						  ts
						-> 
						  let interp = Hashtbl.create 30 in
						  let t_assoc = List.map (fun t -> conv_t interp t,t) ts in
						  let ts = z (conv interp p1) (List.map (conv_t interp) ts)  in
						  List.map (List.map (fun t -> List.assoc t t_assoc)) ts 

						)))
 
*)


   let pprint_proof = Prover.pprint_proof
   let pprint_counter_example = Prover.pprint_counter_example   
   let print_counter_example = Prover.print_counter_example
   let get_counter_example = Prover.get_counter_example
   let string_of_proof = Prover.string_of_proof
