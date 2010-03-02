open Vars
(*open Rterm *)
open Pterm
open Plogic 




(***************************************************
 from prover
***************************************************)


type varterm = 
    Var of varset

type where = 
  | NotInContext of varterm
  | NotInTerm of varterm * args

let string_vs ppf vs =
  vs_iter (fun v -> Format.fprintf ppf "%s" (string_var v)) vs

let string_where ppf where = 
  match where with 
    NotInContext (Var vs) -> 
      Format.fprintf ppf "%a notincontext" 
	string_vs vs
  | NotInTerm (Var vs, args) -> 
      Format.fprintf ppf "%a notin %a" 
	string_vs vs 
	string_args args



type sequent_rule = psequent * (psequent list list) * string * ((* without *) pform * pform) * (where list)

let string_pseq ppf (g,l,r) = 
  Format.fprintf ppf "%a@ | %a@ |- %a" 
    Plogic.string_form g 
    Plogic.string_form l
    Plogic.string_form r

let string_psr ppf (sr :sequent_rule) : unit = 
    match sr with 
      (conclusion, premises, name, (without1,without2), where) ->
	Format.fprintf ppf 
	  "rule %s:@\n%a@\n%a@\nwithout@\n %a@ |- %a@\n%a"
	  name
	  string_pseq conclusion
	  (Debug.list_format_optional "if\n " " or " (Debug.list_format ";" string_pseq)) premises
	  string_form without1
	  string_form without2
	  (Debug.list_format_optional "where" ";" string_where) where
	  




type 'a rewrite_entry =  (args list * args * 'a * string * bool) list

(* substitution *)
(*IF-OCAML*)
module RewriteMap =
  Map.Make(struct
    type t = string
    let compare = compare
  end)
type 'a rewrite_map =  'a rewrite_entry RewriteMap.t 
(*ENDIF-OCAML*)

(*F#
module RewriteMap = Map
type 'a rewrite_map =  RewriteMap.t<string,'a rewrite_entry> 
F#*)

let rm_empty = RewriteMap.empty
let rm_add = RewriteMap.add
let rm_find = RewriteMap.find



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
