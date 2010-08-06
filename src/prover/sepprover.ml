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

(*
    (*************************************
       Syntactic representation of terms
    **************************************)
    let debug f = Debug.debug_ref := f
    
    type var = Vars.var

    let prog_var (n : string) : var = (Vars.concretep_str n)

    let exists_var (n : string) : var = (Vars.concretee_str n)
  
    let fresh_exists_var () : var = (Vars.freshe ()) 

    let fresh_unify_var () : var = (Vars.fresha ()) 

    let fresh_prog_var () : var = (Vars.freshp ()) 

    let fresh_exists_var_str s : var = (Vars.freshe_str s) 

    let fresh_prog_var_str s : var = (Vars.freshp_str s) 
    
    (* Used in rules for pattern matching *)
    let unify_var (n : string) : var = (Vars.fresha_str n)

    type term = Psyntax.args

    let mkVar : var -> term = fun x -> Arg_var x

    let mkFun : string -> term list -> term = fun n tl -> Arg_op(n, tl)

    let mkString : string -> term = fun n -> Arg_string(n)

    (*************************************
       Syntactic representation of formula
    **************************************)
    type form  = Psyntax.pform

    (* False *)
    let mkFalse : form = Psyntax.mkFalse

    (* Inequality between two terms *)
    let mkNEQ : term * term -> form = fun (a1,a2) ->  Psyntax.mkNEQ(a1,a2)

    (* Equality between two terms *)
    let mkEQ : term * term -> form = fun (a1,a2) -> Psyntax.mkEQ(a1,a2)

    (* A pure predicate *)
    let mkPPred : string * term list -> form 
        = fun (n,al) -> Psyntax.mkPPred(n, al)

    (* A spatial predicate *)
    let mkSPred : string * term list -> form 
        = fun (n,al) ->  Psyntax.mkSPred(n, al)

    (* Disjunction of two formula *)
    let mkOr : form * form -> form  = fun (f1, f2) ->Psyntax.mkOr(f1,f2)

    (* Star conjunction of two formula *)
    let mkStar : form -> form -> form = fun f1 f2 -> Psyntax.pconjunction f1 f2

    (* Empty formula/heap*)
    let mkEmpty : form = Psyntax.mkEmpty
    
    (***************************************
       Free variable functions
     ***************************************)
    type varset = Psyntax.varset

    let vs_mem : var -> varset -> bool 
	= fun v vs -> Psyntax.vs_mem v vs

    let vs_add : var -> varset -> varset 
	= fun v vs -> (Psyntax.vs_add v vs)

    let vs_empty : varset 
	= Psyntax.vs_empty

    let vs_fold : (var -> 'a -> 'a) -> varset -> 'a -> 'a 
      = fun f vs x -> Psyntax.vs_fold (fun v x -> f v x) vs x 

    let vs_iter : (var -> unit) -> varset -> unit 
      = fun f vs -> Psyntax.vs_iter (fun v -> f v) vs

    let vs_diff : varset -> varset -> varset 
      = fun vs1  vs2 -> Psyntax.vs_diff vs1 vs2 

    let vs_exists : (var -> bool) -> varset -> bool 
      = fun f vs -> Psyntax.vs_exists (fun v -> f v) vs 

    (* returns the set of free variables  in the term *)
    let fv_form : form -> varset 
      = fun f -> Psyntax.fv_form f Psyntax.vs_empty

    (* returns the set of existential variables in the term *)
    let ev_form : form -> varset 
      = fun f -> Psyntax.ev_form f Psyntax.vs_empty



    (***************************************
     *  Pretty print functions
     ***************************************)

    let string_form : Format.formatter -> form -> unit 
	= fun ppf form -> Psyntax.string_form ppf form 
    
    
    (***************************************
     Substitution on formula 
     ***************************************)

    (* Substitution on terms *)
    type var_subst 
      = Psyntax.varmap

    (* Creates the empty variable substitution *)
    let empty_subst : var_subst 
      = Psyntax.empty

    (* Adds a variable to a substitution *)
    let add_subst : var -> term -> var_subst -> var_subst 
      = fun  v t vs -> Psyntax.add v t vs
     
    (* Makes a substitution freshen all variables it 
       does have a substitution for *)
    let freshening_subst : var_subst -> var_subst = fun vs -> Psyntax.freshening_subs vs


    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh program variable *)
    let subst_kill_vars_to_fresh_prog : varset -> var_subst
      = fun vs -> Psyntax.subst_kill_vars_to_fresh_prog vs
      
    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh exists variable *)      
    let subst_kill_vars_to_fresh_exist : varset -> var_subst  
      = fun vs -> Psyntax.subst_kill_vars_to_fresh_exist vs

    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh variable of the same sort*)          
    let subst_freshen_vars : varset -> var_subst 
      = fun vs -> Psyntax.subst_freshen_vars vs
    
    (* Use a substitution on a formula *)
    let subst_form : var_subst -> form -> form =
      fun vs form -> Psyntax.subst_pform vs form      
*)
    (*****************************************
       Internal formula operations
     *****************************************)

    type inner_form = Clogic.ts_formula

    let inner_truth =  Clogic.mk_ts_form (Cterm.new_ts ()) Clogic.truth 

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

    let kill_var : var -> inner_form -> inner_form
      = fun v inner_form -> 
	Clogic.kill_var inner_form v(* Rlogic.kill_var v inner_form *)

    let kill_all_exists_names : inner_form -> inner_form
	= fun iform -> iform (*assert false  (* TODO. Should do some form of compression of formula *) (*Rlogic.kill_all_exists_names *)*)

    let update_var_to : var -> term -> inner_form -> inner_form
      = fun v e f -> Clogic.update_var_to f v e (* Rlogic.update_var_to x y z*)

    let form_clone : inner_form -> inner_form 
      = fun inner_form -> inner_form  (* functional rep now, so easy *)

    let form_clone_abs : inner_form -> inner_form 
      = fun inner_form -> inner_form  (* TODO. Should do some form of compression of formula *)


    let string_inner_form : Format.formatter -> inner_form -> unit = 
      Clogic.pp_ts_form 
     
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

    let implies_inner : logic -> inner_form -> inner_form -> bool 
      = fun logic inner_form1 inner_form2 -> Prover.check_implication logic inner_form1 inner_form2

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
         (i2 : inner_form )
         : inner_form list option
         = 
	Prover.check_frame l i1 i2

    let abs : logic -> inner_form -> inner_form list 
      = Prover.abs

    let abs_opt : logic -> inner_form option -> inner_form list 
      = fun l form -> match form with None -> [] | Some form -> Prover.abs l form

    let implies_list : inner_form list -> form -> bool 
	= Prover.check_implies_list 

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
   let string_of_proof = Prover.string_of_proof
