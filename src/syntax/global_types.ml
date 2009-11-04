open Jparsetree
open Vars
open Spec_def
(*open Rterm *)
open Pterm
open Plogic 
open Rlogic
open Prover

type 'a importoption =
    ImportEntry of string 
  | NormalEntry of 'a

type spec_file = class_spec importoption list 

(*
module ClassMap =   
  Map.Make(struct
    type t = class_name
    let compare = compare
  end)


type excep_post = Plogic.pform ClassMap.t 

type spec = 
    { pre : Plogic.pform;
      post : Plogic.pform;
      excep : excep_post }

type methodspec =
      Dynamic of method_signature_short * (spec list)
  |   Static of method_signature_short * (spec list)

type methodspecs =
    methodspec list

type apf_define = (string * var * fldlist * Plogic.pform * bool)

type apf_defines = apf_define list

type class_spec = (class_name * apf_defines * methodspecs)

type spec_file = class_spec importoption list 
*)



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

type core_statement = 
  | Nop_stmt_core
  | Label_stmt_core of  label_name 
  | Assignment_core of variable list * spec * immediate list option 
  | If_stmt_core of expression * label_name 
  | Goto_stmt_core of label_name  
  | Throw_stmt_core of immediate



type stmt_core = { 
  (*labels: labels; *)
  mutable skind: core_statement;
  mutable sid: int;  (* this is filled when the cfg is done *)
  mutable succs: stmt_core list; (* this is filled when the cfg is done *)
  mutable preds: stmt_core list  (* this is filled when the cfg is done *)
 }


type methdec = {
 modifiers: modifier list;
 class_name: Jparsetree.class_name;
 ret_type:j_type;
 name_m: name; 
 params: parameter list; 
 locals: local_var list;
 th_clause:throws_clause;
 mutable bstmts: stmt_core list; (* this is set after the call of cfg *)
}

let mk_methdec  ml cn ty n pl ll tc stm =
{ modifiers=ml;
  class_name=cn;
  ret_type=ty;
  name_m=n; 
  params= pl; 
  locals= ll;
  th_clause=tc;
  bstmts=stm; 
}


let mk_stmt_core skind sid succs preds =
  { 
     skind=skind;
     sid=sid;
     succs=succs;
     preds=preds;
 }

(*
let mk_spec  pre post excep = 
    { pre=pre;
      post=post;
      excep=excep
    }

*)
