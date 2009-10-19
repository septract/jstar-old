open Jparsetree
open Vars
(*open Rterm *)
open Pterm
open Plogic 
open Rterm
open Rlogic
open Prover

type 'a importoption =
    ImportEntry of string 
  | NormalEntry of 'a



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
(***************************************************
 end from rlogic
***************************************************)




(***************************************************
 from prover
***************************************************)




type rewrite_rule = string * representative args list * representative args * (representative pform) * (where list) * (representative pform) (* if *) * string * bool

type equiv_rule = string * (representative pform) * (representative pform) * (representative pform) * (representative pform)

type rules = 
  | SeqRule of sequent_rule
  | RewriteRule of rewrite_rule
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
