open Jparsetree
open Vars
(*open Rterm *)
open Pterm
open Plogic 

(***************************************************
 from rterm
***************************************************)

(* terms that only refer to representatives for subterms. *)
type flattened_term = 
    FTConstr of string * representative list
  | FTFunct of string * representative list
  | FTRecord of (string * representative) list
  | FTString of string
  | FTPVar of Vars.var  (* Not sure we need existential variables *)
and representative =
    rep_record ref
and rep_record =
    {
     mutable terms: term list;
     mutable uses: term list;
     n: int;
     name: string;
     mutable deleted: bool;
   }
and term = term_record ref 
and term_record =
   {
    mutable redundant : bool;
    mutable righthand : bool;
    mutable term : flattened_term;
    mutable rep : representative;
    nn : int;
   }
    
(***************************************************
 end from rterm
***************************************************)

module ClassMap =   
  Map.Make(struct
    type t = class_name
    let compare = compare
  end)


type excep_post = representative Plogic.pform ClassMap.t 

type spec = 
    { pre : representative Plogic.pform;
      post : representative Plogic.pform;
      excep : excep_post }

type methodspec =
      Dynamic of method_signature_short * (spec list)
  |   Static of method_signature_short * (spec list)

type methodspecs =
    methodspec list

type apf_define = (string * var * representative fldlist * representative Plogic.pform * bool)

type apf_defines = apf_define list

type class_spec = (class_name * apf_defines * methodspecs)

type spec_file = class_spec list 


(***************************************************
 from rlogic
***************************************************)
type varterm = 
    Var of varset
  | EV of representative args

type where = 
  | NotInContext of varterm
  | NotInTerm of varterm * representative args
(***************************************************
 end from rlogic
***************************************************)




(***************************************************
 from prover
***************************************************)
type sequent_rule = representative psequent * (representative psequent list list) * string * (representative pform) * (where list)

type rewrite_rule = string * representative args list * representative args * (representative pform) * (where list) * (representative pform) (* if *) * string * bool

type equiv_rule = string * (representative pform) * (representative pform) * (representative pform) * (representative pform)

type rules = 
  | SeqRule of sequent_rule
  | RewriteRule of rewrite_rule
  | Import of string
  | EquivRule of equiv_rule


type question =
  |  Implication of representative pform * representative pform 
  |  Inconsistency of representative pform
  |  Frame of representative pform * representative pform
  |  Equal of representative pform * representative args * representative args
  |  Abs of representative pform 


type test =
  |  TImplication of representative pform * representative pform * bool 
  |  TInconsistency of representative pform * bool 
  |  TFrame of representative pform * representative pform * representative pform 
  |  TEqual of representative pform * representative args * representative args * bool
  |  TAbs of representative pform * representative pform


let expand_equiv_rules rules = 
(*encode equiv rule as three rules *)
  let equiv_rule_to_seq_rule x list : rules list= 
    match x with 
      EquivRule(name, guard, leftform, rightform, without) -> 
	let lhs_rule = SeqRule((guard, leftform, []), [[([],rightform,[])]],name ^ "_left", without, []) in 
	let rhs_rule = SeqRule(([],[],guard&&&leftform), [[([],[],guard&&&rightform)]], name ^"_right", without, []) in 
	let spl_rule = SeqRule((guard, [], leftform), [[([],[],rightform)]], name ^ "_split", without, []) in 
	lhs_rule::rhs_rule::spl_rule::list
    | _ -> x::list
  in
  List.fold_right equiv_rule_to_seq_rule rules []

(***************************************************
 end from prover
***************************************************)
