(*F#
namespace Microsoft.Research.Vcc2
F#*)

open Debug
open Global_types

module SepProver = struct

    (*************************************
       Syntactic representation of terms
    **************************************)
    let debug f = Debug.debug_ref := f
    
    type var = Var of Vars.var

    let prog_var (n : string) : var = Var (Vars.concretep_str n)

    let exists_var (n : string) : var = Var (Vars.concretee_str n)
  
    let fresh_exists_var () : var = Var (Vars.freshe ()) 

    let fresh_unify_var () : var = Var (Vars.fresha ()) 

    let fresh_prog_var () : var = Var (Vars.freshp ()) 

    let fresh_exists_var_str s : var = Var (Vars.freshe_str s) 

    let fresh_prog_var_str s : var = Var (Vars.freshp_str s) 
    
    (* Used in rules for pattern matching *)
    let unify_var (n : string) : var = Var (Vars.fresha_str n)

    type term = Term of representative Pterm.args

    let unterm = (fun (Term a) -> a) 
    let unterm_list = List.map unterm 

    let mkVar : var -> term = fun (Var x) -> Term (Pterm.Arg_var x)

    let mkFun : string -> term list -> term = fun n tl -> Term (Pterm.Arg_op(n,unterm_list tl))

    let mkString : string -> term = fun n -> Term (Pterm.Arg_string(n))

    (*************************************
       Syntactic representation of formula
    **************************************)
    type form  = Form of representative Plogic.pform

    let unform = fun (Form x) -> x 

    (* False *)
    let mkFalse : form = Form Plogic.mkFalse

    (* Inequality between two terms *)
    let mkNEQ : term * term -> form = fun (Term a1,Term a2) ->  Form (Plogic.mkNEQ(a1,a2))

    (* Equality between two terms *)
    let mkEQ : term * term -> form = fun (Term a1,Term a2) ->  Form (Plogic.mkEQ(a1,a2))

    (* A pure predicate *)
    let mkPPred : string * term list -> form 
        = fun (n,al) ->  Form (Plogic.mkPPred(n,unterm_list al))

    (* A spatial predicate *)
    let mkSPred : string * term list -> form 
        = fun (n,al) ->  Form (Plogic.mkSPred(n,unterm_list al))

    (* Disjunction of two formula *)
    let mkOr : form * form -> form  = fun (Form f1, Form f2) -> Form (Plogic.mkOr(f1,f2))

    (* Star conjunction of two formula *)
    let mkStar : form -> form -> form = fun (Form f1) (Form f2) -> Form (Plogic.pconjunction f1 f2)

    (* Empty formula/heap*)
    let mkEmpty : form = Form (Plogic.mkEmpty)
    
    (***************************************
       Free variable functions
     ***************************************)
    type varset = VS of Pterm.varset

    let vs_mem : var -> varset -> bool = fun (Var v) (VS vs) -> Pterm.vs_mem v vs
    let vs_add : var -> varset -> varset = fun (Var v) (VS vs) -> VS(Pterm.vs_add v vs)
    let vs_empty : varset = VS Pterm.vs_empty
    let vs_fold : (var -> 'a -> 'a) -> varset -> 'a -> 'a 
      = fun f (VS vs) x -> Pterm.vs_fold (fun v x -> f (Var v) x) vs x 
    let vs_iter : (var -> unit) -> varset -> unit 
      = fun f (VS vs) -> Pterm.vs_iter (fun v -> f (Var v)) vs
    let vs_diff : varset -> varset -> varset 
      = fun (VS vs1) (VS vs2) -> VS(Pterm.vs_diff vs1 vs2) 
    let vs_exists : (var -> bool) -> varset -> bool 
      = fun f (VS vs) -> Pterm.vs_exists (fun v -> f (Var v)) vs 

    (* returns the set of free variables  in the term *)
    let fv_form : form -> varset = fun (Form f) -> VS(Plogic.fv_form f Pterm.vs_empty)

    (* returns the set of existential variables in the term *)
    let ev_form : form -> varset = fun (Form f) -> VS(Plogic.ev_form f Pterm.vs_empty)



    (***************************************
     *  Pretty print functions
     ***************************************)

    let string_form : Format.formatter -> form -> unit = fun (ppf) (Form form) -> Plogic.string_form ppf form 
    
    
    (***************************************
     Substitution on formula 
     ***************************************)

    (* Substitution on terms *)
    type var_subst = VSub of representative Pterm.varmap

    (* Creates the empty variable substitution *)
    let empty_subst : var_subst = VSub (Pterm.empty)

    (* Adds a variable to a substitution *)
    let add_subst : var -> term -> var_subst -> var_subst = fun (Var v) (Term t) (VSub vs) -> VSub (Pterm.add v t vs)
     
    (* Makes a substitution freshen all variables it 
       does have a substitution for *)
    let freshening_subst : var_subst -> var_subst = fun (VSub vs) -> VSub (Pterm.freshening_subs vs)


    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh program variable *)
    let subst_kill_vars_to_fresh_prog : varset -> var_subst
      = fun (VS vs) -> VSub (Pterm.subst_kill_vars_to_fresh_prog vs)
      
    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh exists variable *)      
    let subst_kill_vars_to_fresh_exist : varset -> var_subst  
      = fun (VS vs) -> VSub (Pterm.subst_kill_vars_to_fresh_exist vs)

    (* Builds a substitution which replaces each variable 
       in the supplied set with a fresh variable of the same sort*)          
    let subst_freshen_vars : varset -> var_subst 
      = fun (VS vs) -> VSub (Pterm.subst_freshen_vars vs)
    
    (* Use a substitution on a formula *)
    let subst_form : var_subst -> form -> form =
      fun (VSub vs) (Form form) -> Form (Plogic.subst_pform vs form)
      

    (*****************************************
       Internal formula operations
     *****************************************)

    type rform = RForm of Rlogic.ts_form

    let convert : form -> rform  = fun (Form form) -> RForm (Rlogic.convert form)

    let conjoin : form -> rform -> rform = fun (Form form) (RForm rform) -> RForm (Rlogic.conj_convert form rform)

    let kill_var : var -> rform -> unit = fun (Var v) (RForm rform) -> Rlogic.kill_var v rform

    let update_var_to : var -> term -> rform -> unit = fun (Var x) (Term y) (RForm z) -> Rlogic.update_var_to x y z;()

    let form_clone : rform -> rform = fun (RForm rform) -> RForm (Rlogic.form_clone rform false)



    (*******************************************
        Logic operations
     ******************************************)

    type logic = Logic of Prover.logic

    type sequent = form * form * form
    let seq_con (Form f1,Form f2,Form f3) = (f1,f2,f3)
    let premises_con = List.map (List.map seq_con)

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

    let empty_logic = Logic (Prover.empty_logic)

    let add_rewrite_rule (rr : rewrite_rule) (Logic (sl,rm,ep) : logic) : logic = 
      Logic (sl,Rterm.rm_add rr.op ((unterm_list rr.arguments,unterm rr.new_term,([],[],[]),rr.rule_name,false)::(try Rterm.rm_find rr.op rm with Not_found -> [])) rm,ep)
      

    let add_sequent_rule (sr : sequent_rule) (Logic (sl,rm,ep) : logic) : logic =
      let sr = ((seq_con sr.conclusion,premises_con sr.premises,sr.name,unform sr.without,[])) in
(*      Printf.printf "Adding rule: \n%s" (Prover.string_psr sr) ;*)
      Logic (sl @ [sr] , rm, ep)
     
    (******************************************
       Entailment operations
     ******************************************)

    let implies : logic -> rform -> rform -> bool = fun (Logic logic) (RForm rform1) (RForm rform2) -> Prover.check_implication logic rform1 rform2

    let rform_lift = List.map (fun x-> RForm x)  
    let frame : logic -> rform -> form -> rform list = fun (Logic logic) (RForm rform1) (Form form2) -> rform_lift (Prover.check_implication_frame_pform logic rform1 form2)

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
 

  end
