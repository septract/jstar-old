(*F#
namespace Microsoft.Research.Vcc2
F#*)

open Debug
open Rterm
open Jimple_global_types

module SepProver = struct

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

    type term = Pterm.args

    let mkVar : var -> term = fun x -> Arg_var x

    let mkFun : string -> term list -> term = fun n tl -> Arg_op(n, tl)

    let mkString : string -> term = fun n -> Arg_string(n)

    (*************************************
       Syntactic representation of formula
    **************************************)
    type form  = Plogic.pform

    (* False *)
    let mkFalse : form = Plogic.mkFalse

    (* Inequality between two terms *)
    let mkNEQ : term * term -> form = fun (a1,a2) ->  Plogic.mkNEQ(a1,a2)

    (* Equality between two terms *)
    let mkEQ : term * term -> form = fun (a1,a2) -> Plogic.mkEQ(a1,a2)

    (* A pure predicate *)
    let mkPPred : string * term list -> form 
        = fun (n,al) -> Plogic.mkPPred(n, al)

    (* A spatial predicate *)
    let mkSPred : string * term list -> form 
        = fun (n,al) ->  Plogic.mkSPred(n, al)

    (* Disjunction of two formula *)
    let mkOr : form * form -> form  = fun (f1, f2) ->Plogic.mkOr(f1,f2)

    (* Star conjunction of two formula *)
    let mkStar : form -> form -> form = fun f1 f2 -> Plogic.pconjunction f1 f2

    (* Empty formula/heap*)
    let mkEmpty : form = Plogic.mkEmpty
    
    (***************************************
       Free variable functions
     ***************************************)
    type varset = Pterm.varset

    let vs_mem : var -> varset -> bool 
	= fun v vs -> Pterm.vs_mem v vs

    let vs_add : var -> varset -> varset 
	= fun v vs -> (Pterm.vs_add v vs)

    let vs_empty : varset 
	= Pterm.vs_empty

    let vs_fold : (var -> 'a -> 'a) -> varset -> 'a -> 'a 
      = fun f vs x -> Pterm.vs_fold (fun v x -> f v x) vs x 

    let vs_iter : (var -> unit) -> varset -> unit 
      = fun f vs -> Pterm.vs_iter (fun v -> f v) vs

    let vs_diff : varset -> varset -> varset 
      = fun vs1  vs2 -> Pterm.vs_diff vs1 vs2 

    let vs_exists : (var -> bool) -> varset -> bool 
      = fun f vs -> Pterm.vs_exists (fun v -> f v) vs 

    (* returns the set of free variables  in the term *)
    let fv_form : form -> varset 
      = fun f -> Plogic.fv_form f Pterm.vs_empty

    (* returns the set of existential variables in the term *)
    let ev_form : form -> varset 
      = fun f -> Plogic.ev_form f Pterm.vs_empty



    (***************************************
     *  Pretty print functions
     ***************************************)

    let string_form : Format.formatter -> form -> unit 
	= fun ppf form -> Plogic.string_form ppf form 
    
    
    (***************************************
     Substitution on formula 
     ***************************************)

    (* Substitution on terms *)
    type var_subst 
      = Pterm.varmap

    (* Creates the empty variable substitution *)
    let empty_subst : var_subst 
      = Pterm.empty

    (* Adds a variable to a substitution *)
    let add_subst : var -> term -> var_subst -> var_subst 
      = fun  v t vs -> Pterm.add v t vs
     
    (* Makes a substitution freshen all variables it 
       does have a substitution for *)
    let freshening_subst : var_subst -> var_subst = fun vs -> Pterm.freshening_subs vs


    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh program variable *)
    let subst_kill_vars_to_fresh_prog : varset -> var_subst
      = fun vs -> Pterm.subst_kill_vars_to_fresh_prog vs
      
    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh exists variable *)      
    let subst_kill_vars_to_fresh_exist : varset -> var_subst  
      = fun vs -> Pterm.subst_kill_vars_to_fresh_exist vs

    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh variable of the same sort*)          
    let subst_freshen_vars : varset -> var_subst 
      = fun vs -> Pterm.subst_freshen_vars vs
    
    (* Use a substitution on a formula *)
    let subst_form : var_subst -> form -> form =
      fun vs form -> Plogic.subst_pform vs form      

    (*****************************************
       Internal formula operations
     *****************************************)

    type rform = Rlogic.ts_form

    let convert : form -> rform  
      = fun form -> Rlogic.convert form

    let conjoin : form -> rform -> rform 
      = fun form rform -> Rlogic.conj_convert form rform

    let kill_var : var -> rform -> unit 
      = fun v rform -> Rlogic.kill_var v rform

    let update_var_to : var -> term -> rform -> unit 
      = fun x y z -> ignore (Rlogic.update_var_to x y z)

    let form_clone : rform -> rform 
      = fun rform -> Rlogic.form_clone rform false



    (*******************************************
        Logic operations
     ******************************************)

    type logic = Prover.logic

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

    let empty_logic = Prover.empty_logic

    let add_rewrite_rule (rr : rewrite_rule) ((sl,rm,ep) : logic) : logic = 
      (sl,
       Rterm.rm_add rr.op ((rr.arguments,rr.new_term,([],[],[]),rr.rule_name,false)
			   ::(try Rterm.rm_find rr.op rm with Not_found -> [])) 
	 rm,
       ep)
      

    let add_sequent_rule (sr : sequent_rule) ((sl,rm,ep) : logic) : logic =
      let sr = ((sr.conclusion,sr.premises,sr.name,(sr.without,[]),[])) in
(*      Printf.printf "Adding rule: \n%s" (Prover.string_psr sr) ;*)
      (sl @ [sr] , rm, ep)
     
    (******************************************
       Entailment operations
     ******************************************)

    let implies : logic -> rform -> rform -> bool 
      = fun logic rform1 rform2 -> Prover.check_implication logic rform1 rform2

    let frame : logic -> rform -> form -> rform list 
      = fun logic rform1 form2 -> 
	Prover.check_implication_frame_pform logic rform1 form2

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
        | Pterm.Arg_string n -> String n
        | Pterm.Arg_op (n,al) -> Fun(n, List.map (conv_t interp) al)
        | Pterm.Arg_var (Vars.PVar(v,n)) -> PVar (Vars.string_var (Vars.PVar(v,n))) 
        | Pterm.Arg_var (Vars.EVar(v,n)) -> EVar (Vars.string_var (Vars.EVar(v,n))) 
        | _ -> Printf.printf "Don't know how to convert this term to external use."; unsupported ()
      in Hashtbl.add interp a v; v
      
    let rec conv interp (pl : representative Plogic.pform) : out_form = 
      let conv_t = conv_t interp in 
      match pl with
        [] -> TT 
      | Plogic.P_EQ(a1,a2)::pl -> And (EQ(conv_t a1, conv_t a2), conv interp pl) 
      | Plogic.P_NEQ(a1,a2)::pl -> And (NEQ(conv_t a1, conv_t a2), conv interp pl) 
      | Plogic.P_PPred(name,al)::pl -> And (Pred(name,List.map conv_t al), conv interp pl) 
      | Plogic.P_Or(p1,p2)::pl -> And(Or(conv interp p1, conv interp p2), conv interp pl)
      | Plogic.P_False::pl -> FF
      | _ -> Printf.printf "Don't know how to convert this formula to external use.\n"; unsupported ()

    let add_external_prover : logic -> (out_form -> out_form -> bool) -> logic =
      fun (Logic (x,y,(ep1,ep2))) z -> Logic (x,y,
					      ((fun (p1 : representative Plogic.pform) 
						  (p2 : representative Plogic.pform) 
						-> let interp = Hashtbl.create 30 in z (conv interp p1) (conv interp p2))
						,ep2))
 
    let add_external_congruence : logic -> (out_form -> out_term list -> out_term list list) -> logic
	=
      fun (Logic (x,y,(ep1,ep2))) z -> Logic (x,y,
					      (ep1,(fun (p1 : representative Plogic.pform) 
						  ts
						-> 
						  let interp = Hashtbl.create 30 in
						  let t_assoc = List.map (fun t -> conv_t interp t,t) ts in
						  let ts = z (conv interp p1) (List.map (conv_t interp) ts)  in
						  List.map (List.map (fun t -> List.assoc t t_assoc)) ts 

						)))
 
*)
  end
