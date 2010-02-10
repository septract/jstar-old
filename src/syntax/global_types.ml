open Jparsetree
open Vars
open Spec_def
(*open Rterm *)
open Pterm
open Plogic 
open Rlogic
open Prover
open Prover_types

type 'a importoption =
    ImportEntry of string 
  | NormalEntry of 'a

type spec_file = class_spec importoption list 




(***************************************************
 from prover
***************************************************)




type rewrite_rule = string * args list * args * (pform) * (where list) * (pform) (* if *) * string * bool

type equiv_rule = string * (pform) * (pform) * (pform) * (pform)

type rules = 
  | SeqRule of sequent_rule
  | RewriteRule of rewrite_rule
  | EquivRule of equiv_rule

type question =
  |  Implication of pform * pform 
  |  Inconsistency of pform
  |  Frame of pform * pform
  |  Equal of pform * args * args
  |  Abs of pform 


type test =
  |  TImplication of pform * pform * bool 
  |  TInconsistency of pform * bool 
  |  TFrame of pform * pform * pform 
  |  TEqual of pform * args * args * bool
  |  TAbs of pform * pform


let expand_equiv_rules rules = 
(*encode equiv rule as three rules *)
  let equiv_rule_to_seq_rule x list : rules list= 
    match x with 
      EquivRule(name, guard, leftform, rightform, without) -> 
	(SeqRule((guard, leftform, []), [[([],rightform,[])]],name ^ "_left", (without,mkEmpty) , []))
	:: 
	  (SeqRule(([],[],guard&&&leftform), [[([],[],guard&&&rightform)]], name ^"_right", (mkEmpty, without), []))
	::
	  if(guard != []) then 
	    (SeqRule((guard, [], leftform), [[([],[],rightform)]], name ^ "_split", (mkEmpty, without), []))
	    ::
	      list
	  else
	    list
    | SeqRule _ | RewriteRule _ -> x::list
  in
  List.fold_right equiv_rule_to_seq_rule rules []



(***************************************************
 end from prover
***************************************************)


(***************************************************
 from inductive
***************************************************)

type inductive_con =
{
  con_name : string;
  con_def : pform * string * args list
}

type inductive =
{
  ind_name : string;
  ind_args : args list;
  ind_cons : inductive_con list
}

type inductive_stmt = IndImport of string | IndDef of inductive

(***************************************************
 end from inductive
***************************************************)

type tactic_spec =
	| Rule_names of string list
	| Repeat_spec of tactic_spec
	| IfMatch_spec of tactic_spec * tactic_spec * tactic_spec