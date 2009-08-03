(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)
open Debug
open Vars
open Pterm
open Rterm
open Global_types
open Plogic

type plain =
  | EQ of representative * representative
  | NEQ of representative * representative
  | PPred of string * representative list

type spatial =
  | SPred of string * representative list 

type composite =
  | Form of form
  | Wand of composite * composite
  | Or of composite * composite 
  | Septract of composite * composite
  | Garbage
  | False

and form = plain list * spatial list * (composite list)

type ts_form = term_structure * form

let spat_eq s1 s2 =
  match s1 ,s2 with 
  | SPred(n,rl),SPred(n2,rl2) ->
      if n=n2 then List.for_all2 rep_eq rl rl2 else false

let plain_eq p1 p2 =
  match p1 ,p2 with
  | NEQ(r1,r2),NEQ(r3,r4)
  | EQ(r1,r2),EQ(r3,r4) -> rep_eq r1 r3 && rep_eq r2 r4 
  | PPred(n,rl),PPred(n2,rl2) ->
      if n=n2 then List.for_all2 rep_eq rl rl2 else false
  | _,_ -> false

let conjunction (p1,s1,c1) (p2,s2,c2) = 
  match c1,c2 with 
      [False],_ 
    | _,[False] -> ([],[],[False])
    | _, _ -> (p1@p2,s1@s2,c1@c2)
    

let disjunction (p1,s1,c1) (p2,s2,c2) = ([], [], [Or(Form(p1,s1,c1),Form(p2,s2,c2))])

let wand (p1,s1,c1) (p2,s2,c2) = ([], [], [Wand(Form(p1,s1,c1),Form(p2,s2,c2))])
  
let (@@@) : form -> form -> form = conjunction





(* Probably want to be careful so identifiers and strings are dealt with correctly *)
let compare_plain  ca1 ca2 = compare ca1 ca2
(*  match ca1 ,ca2 with   
  | EQ(a11,a12),NEQ(a21,a22) -> -1
  | NEQ(a11,a12),EQ(a21,a22) -> 1
  | EQ(a11,a12),EQ(a21,a22) 
  | NEQ(a11,a12),NEQ(a21,a22) ->
      let r = compare a11 a21 in
      if r=0 then 
	compare  a12 a22 
      else r
*)



let subst_plain subs pa =
  match pa with 
   | EQ(a1,a2) -> EQ(apply_subst subs a1, apply_subst subs a2)
   | NEQ (a1,a2) ->
   let a1,a2 = apply_subst subs a1, apply_subst subs a2 in 
   if rep_eq a1 a2 then raise Contradiction else NEQ(a1,a2)
   | PPred(name,args) -> PPred (name,(List.map (apply_subst subs) args))
     
let subst_plain_list subs pl = 
  List.map (subst_plain subs) pl 

let rec subst_spatial subs (sa : spatial) : spatial =
  match sa with 
  | SPred(name,args) -> SPred(name,List.map (apply_subst subs) args)

let subst_spatial_list subs sl =
  List.map (subst_spatial subs) sl

let rec subst_composite subs (c : composite) : composite = 
  match c with 
  | Form f -> (try Form (subst_form subs f) with Contradiction -> False)
  | Or (f1,f2) -> 
      (let f1 = (subst_composite subs f1) in 
      let f2 =(subst_composite subs f2) in
      match f1,f2 with 
      |	False, f 
      | f, False -> f
      | f1, f2 -> Or(f1,f2))
  | Wand (f1,f2) ->
      (let f1 = subst_composite subs f1 in 
       let f2 = subst_composite subs f2 in 
       match f1 with 
       | False -> Garbage
       | _ -> Wand(f1,f2))
  | Septract (f1,f2) ->
      let f1 = subst_composite subs f1 in 
      let f2 = subst_composite subs f2 in 
      (match f1,f2 with
	False,_ -> False
      | _,False -> False
      | _,_ -> Septract (f1,f2))
  | Garbage -> Garbage
  | False -> False

and subst_composite_list subs cl =
  List.map (subst_composite subs) cl

and subst_form subs ((pf,sf,cf) : form) : form =
  let pform = subst_plain_list subs pf in
  let sform = subst_spatial_list subs sf in 
  let cform = subst_composite_list subs cf in  
  let rec inner (pl,sl,cl) cl' =  
    match cl with 
      [] -> (pl,sl,cl')
    | Form(pl1,sl1,cl1) :: cl -> inner (pl1@pl,sl1@sl,cl1@cl) cl' 
    | c::cl -> inner (pl,sl,cl) (c::cl')
  in inner(pform,sform,cform) []
  



(* pretty print *)

let string_plain hash ppf ca =  
  match ca with 
    NEQ(a1,a2) -> Format.fprintf ppf "@[%a != %a@]" (string_rep hash) a1  (string_rep hash) a2
  | EQ(a1,a2) -> Format.fprintf ppf "@[%a = %a@]" (string_rep hash) a1   (string_rep hash) a2 
  | PPred(op,al) -> Format.fprintf ppf "%s(@[%a@])" op (string_rlist hash) al


let string_plain_list hash ppf pl = 
  Debug.list_format " *" (string_plain hash) ppf pl

let string_spatial hash ppf s =
  match s with 
    SPred (s,al) ->  Format.fprintf ppf"%s(@[%a@])" s (string_rlist hash) al 

let string_spatial_list hash ppf sl = 
  Debug.list_format " *" (string_spatial hash) ppf sl


let rec string_combined hash ppf s =
  match s with 
    Form (f) -> Format.fprintf ppf "%a" (string_form hash) f
  | Or(f1,f2) -> Format.fprintf ppf "@[@[(%a)@]@ || @[(%a)@]@]" (string_combined hash) f1 (string_combined hash) f2
  | Wand(f1,f2) -> Format.fprintf ppf "(%a)@ -* (%a)" (string_combined hash) f1   (string_combined hash) f2
  | Septract(f1,f2) -> Format.fprintf ppf "(%a)@ -o (%a)" (string_combined hash) f1   (string_combined hash) f2
  | False -> Format.fprintf ppf "False"
  | Garbage -> Format.fprintf ppf "Garbage"

and string_combined_list hash ppf cl =
  Format.fprintf ppf "%a" (Debug.list_format "*" (string_combined hash)) cl 


(*
and string_spatial_list_nl sl = 
    (String.concat " *\n " (List.map string_spatial sl))
*)

and string_form hash ppf ((pl,sl,cl) : form) = 
  Format.fprintf ppf "@[%a@]@ | @[%a@]@ @[%a@]"
    (string_plain_list hash) pl
    (string_spatial_list hash) sl
    (string_combined_list hash) cl

(*and string_form_nl (pl,sl) = 
  Printf.sprintf "%s |\n %s"
    (string_plain_list pl)
    (string_spatial_list_nl sl)*)

    


let rec rv (rl : representative list) set = 
  List.fold_left (fun set r -> Rset.add r set) set rl
    
let rv_plain plain set =
  match plain with
    EQ(x,y) -> Rset.add y (Rset.add x set)
  | NEQ(x,y) -> Rset.add y (Rset.add x set)
  | PPred(name, rl) -> rv rl set

let rec rv_plain_list pl set = 
  match pl with 
    [] -> set
  | p::pl -> rv_plain_list pl (rv_plain p set)

let rv_spat spat set = 
  match spat with
  | SPred(name, rl) -> rv rl set

let rec rv_spat_list sl set = 
  match sl with 
    [] -> set
  | s::sl -> rv_spat_list sl (rv_spat s set)

let rec rv_comp c set = 
  match c with 
  | Form f -> rv_form f set
  | Wand(f1,f2) 
  | Septract(f1,f2) 
  | Or(f1,f2) -> rv_comp f1 (rv_comp f2 set)
  | Garbage 
  | False -> set
and rv_comp_list cl set = 
  match cl with 
    [] -> set
  | c::cl -> rv_comp_list cl (rv_comp c set)
and rv_form ((pl,sl,cl):form) set =
 rv_spat_list sl (rv_plain_list pl (rv_comp_list cl set))




(* Second type of axiom *)

(* frame, P,S |- P',S' *)
type sequent = spatial list * form * form

type ts_sequent = term_structure * sequent

(*
type varterm = 
    Var of varset
  | EV of representative args

type where = 
  | NotInContext of varterm
  | NotInTerm of varterm * representative args
*)


(*type varterm = 
    Var of varset
  | EV of args

type where = 
  | NotInContext of varterm
  | NotInTerm of varterm * args*)

(* if sequent matches, then replace with each thing  in the sequent list *)
(*type sequent_rule = psequent * (psequent list list) * string * (pplain list) * (where list)*)

(*let string_rule (rule :sequent_rule ) =
  match rule with
    (conc, prem_s_s, name, without, where) ->
      string_seq conc
	*)

(*let mk_seq_rule (mat_seq,premises,name) = 
  mat_seq,premises,name,[],[]

type emp_rule = pspatial * (pplain list) * string

type plain_rule = pspatial list * pplain list list * string

type rewrite_rule = string * args list * args * (pplain list) * (where list) * (pplain list) (* if *) * string

type rules = 
  | SeqRule of sequent_rule
  | EmpRule of emp_rule
  | PureRule of plain_rule
  | RewriteRule of rewrite_rule
  | PredPrecise of string * bool list * string
*)
(*
type rewrite_entry =  (args list * args * (pplain list) * (where list) * (pplain list) * string ) list

(* substitution *)
module RewriteMap =
  Map.Make(struct
    type t = string
    let compare = compare
  end)

type rewrite_map =  rewrite_entry RewriteMap.t 
*)
(* rules for simplifying septraction need defining as well *)

type rewrite_entry_arg =  ((representative Plogic.pform) * (where list) * (representative Plogic.pform)) 

type rewrite_entry_2 = rewrite_entry_arg rewrite_entry

type rewrite_map =  rewrite_entry_arg Rterm.rewrite_map

(* subst on a sequent *)
let f_false = ([],[],[False])

let true_sequent = ([], f_false, ([],[],[]))

(* consider contradiction on right and left *)
let subst_sequent subs (seq : sequent) : sequent =
  match seq with
    framed,left,right ->
      let sf = subst_spatial_list subs framed in 
      let left = try subst_form subs left with Contradiction -> raise Success in
      let right = try subst_form subs right with Contradiction -> f_false in 
      (sf, left, right)
    
let sequent_join (seq1 : sequent) (seq2 : sequent) : sequent =
  match seq1,seq2 with
    (framed1,left1,right1),
    (framed2,left2,right2)
    -> (framed1@framed2,left1 @@@ left2, right1 @@@ right2)


(*type logic = sequent_rule list * emp_rule list * plain_rule list * rewrite_map

(*let empty_logic = [],[],[],RewriteMap.empty *)

let rule_list_to_logic rl =
  let rec rule_list_to_logic_inner rl =
    match rl with
      [] -> ([],[],[],RewriteMap.empty)
    | r :: rl -> let (sl,el,pl,rm) = rule_list_to_logic_inner rl in 
      match r with
      | PredPrecise(p,par,na) -> (sl,el,pl,rm) 
      | EmpRule(r) -> (sl,r::el,pl,rm)
      | SeqRule(r) -> (r::sl,el,pl,rm)
      | PureRule(r) -> (sl,el,r::pl,rm)
      | RewriteRule(r) -> 
	  (match r with 
	    (fn,a,b,c,d,e,f,g) -> (sl,el,pl,RewriteMap.add fn ((a,b,(c,d,e),f,g)::(try RewriteMap.find fn rm with Not_found -> [])) rm))
  in rule_list_to_logic_inner rl 

type question =
  |  Implication of pform * pform 
  |  Inconsistency of pform
  |  Frame of pform * pform
  |  Equal of pform * args * args
  |  Abs of pform 

*)

let rv_sequent ((f,p1,p2) : sequent) = 
  rv_form p1 
    (rv_form p2 
       (rv_spat_list f Rset.empty))

let string_ts_form hash ppf ((ts,f) :ts_form) =
  Format.fprintf ppf "@[@[%a@]@ %s%a@]" 
    (string_ts_rs (rv_form f Rset.empty) hash) ts    
    (match f with ([],_,_) -> "" | _ -> "* ")
    (string_form hash) f

let string_seq hash ppf (f,l,r) = 
  Format.fprintf ppf "@[%a@]@ | @[%a@] @ |- @[%a@]" 
    (Debug.list_format "*" (string_spatial hash)) f
    (string_form hash) l
    (string_form hash) r

let string_ts_seq hash ppf (ts,s) = 
  Format.fprintf ppf "@[%a@ %a@]"
     (string_ts_rs (rv_sequent s) hash) ts  
     (string_seq hash) s





(*   CONVERSION from plogic to rlogic representation *)

let rec pform_at_convert ts (interp : var_subst) (p : representative pform_at) ((pl,sl,cl) : form) : form * var_subst=
 match p with 
 |  P_EQ (a1,a2) -> 
     let r1,interp = add_term ts interp a1 false in 
     let r2,interp = add_term ts interp a2 false in 
     (EQ(r1, r2)::pl,sl,cl),interp
 |  P_NEQ(a1,a2) -> 
     let r1,interp = add_term ts interp a1 false in 
     let r2,interp = add_term ts interp a2 false in 
     (NEQ(r1, r2)::pl,sl,cl), interp
 |  P_PPred(name, al) -> 
     let rl,interp = add_terms ts interp al false in 
     (PPred(name, rl)::pl,sl,cl), interp
  | P_SPred(name, al) -> 
      let rl,interp = add_terms ts interp al false in 
      (pl,SPred(name, rl)::sl,cl),interp
  | P_Wand (f1,f2) -> 
      let f1,interp = pform_convert ts interp f1 in 
      let f2,interp = pform_convert ts interp f2 in 
      (pl,sl,Wand(Form(f1),Form(f2))::cl),interp
  | P_Or (f1,f2) -> 
      let f1,interp = pform_convert ts interp f1 in 
      let f2,interp = pform_convert ts interp f2 in 
      (pl,sl,Or(Form(f1),Form(f2))::cl), interp
  | P_Septract (f1,f2) -> 
      let f1,interp = pform_convert ts interp f1 in 
      let f2,interp = pform_convert ts interp f2 in 
      (pl,sl,Septract(Form(f1), Form(f2))::cl), interp
  | P_Garbage -> (pl,sl,Garbage::cl), interp 
  | P_False  ->  ([],[],[False]), interp
and pform_convert ts (interp : var_subst) (pf : representative pform) : form * var_subst=
  List.fold_left (fun (pf,interp) pa -> pform_at_convert ts interp pa pf) (([],[],[]),interp) pf


let convert (f : representative pform) : ts_form =
  let ts = Rterm.blank () in 
  let f,interp = (pform_convert ts (Rterm.empty_vs) f) in 
  ts, f

let conj_convert (pf : representative pform) ((ts,f) : ts_form) : ts_form =
  let f,interp = List.fold_left (fun (pf,interp) pa -> pform_at_convert ts interp pa pf) 
      (f,Rterm.empty_vs) pf in 
  ts, f

let psequent_convert ts interp ((fr,f1,f2) : representative psequent) : sequent =
  let fr,interp = pform_convert ts interp fr in
  let f1,interp = pform_convert ts interp f1 in 
  let f2,interp = pform_convert ts interp f2 in 
  match fr with 
    ([],fr,[]) -> (fr,f1,f2)
  | _ -> unsupported ()





(*  Interface stuff for symbolic execution *)
let kill_var v (form : ts_form) : unit = 
  let ts,f = form in 
  Rterm.kill_var ts v 

let kill_all_exists_names (form : ts_form) : unit =
  let ts,f = form in
  Rterm.kill_all_exists_names ts

let update_var_to v e (form : ts_form) : ts_form = 
  let ts,f = form in 
  let r2,subs = add_term ts Rterm.empty_vs e false in 
  Rterm.kill_var ts v;
  let r1,subs = add_term ts Rterm.empty_vs (Arg_var v) false in 
(*  assert(subs=Rterm.empty);*)
(*  assert(subs=Rterm.empty);*)
  let subs = add_equal ts r2 r1 in
  (ts,subst_form subs f)
  (* Check no updates necessary *)

let form_clone ((ts,form) : ts_form)  abs
    =
(*  if ts_debug then Printf.printf "Cloning: \n%s\n" (string_ts_form (ts,form));  *)
  let ts,subs = clone ts (rv_form form Rset.empty) abs in 
  try 
    let res = (ts,subst_form subs form) in
(*    if ts_debug then Printf.printf "Results in: \n%s\n" (string_ts_form res); *)
    res
  with Contradiction ->
    (ts,f_false)


(*********************************************
  ts_form to plain pform 
 *********************************************)
 
 let form_to_plain_pform interp rs hash ts pl : representative pform =
   let pterm_rep = pterm_rep interp rs hash in 
   let ftpp c = 
	match c with
	  EQ(r1,r2) -> P_EQ(pterm_rep r1, pterm_rep r2)
	| NEQ(r1,r2) -> P_NEQ(pterm_rep r1, pterm_rep r2)
	| PPred(name,rl) -> P_PPred(name, pterm_rlist interp rs hash rl) in
	List.map ftpp pl	

let rec form_is_plain interp rs ts hash f =
  match f with 
    (pl,[],cl) -> 
      let cl = (composite_list_is_plain interp rs ts hash cl) in
      (match cl with 
        None -> None
       |Some cl -> 
          Some ((form_to_plain_pform interp rs ts hash pl) @ cl ) )
  | (pl,sl,cl) -> None
and composite_is_plain interp rs ts hash c =
  match c with 
  | Or(f1,f2) -> 
    let f1 = composite_is_plain interp rs ts hash f1 in 
    let f2 = composite_is_plain interp rs ts hash f2 in 
    (match f1,f2 with Some f1, Some f2 -> Some ([P_Or(f1,f2)]) | _ -> None)
  | Form(f1) -> 
     form_is_plain interp rs ts hash f1
  | False -> Some [P_False]
  | _ -> None
and composite_list_is_plain interp rs ts hash cl = 
  match (map_lift_forall (composite_is_plain interp rs ts hash) cl) with
  | None -> None
  | Some n -> Some (List.flatten n) 
	
	
	
let ts_form_plain_pform interp hash (ts,form) : representative pform = 
  let rs = rv_plain_list form Rset.empty in 
  (pform_ts_rs_left interp ts hash rs rs) @ (form_to_plain_pform interp rs hash ts form)

let ts_form_plain_pform_rs interp hash (ts,form) rs : representative pform = 
  (pform_ts_rs_left interp ts hash rs rs) @ (form_to_plain_pform interp rs hash ts form)
  
let ts_sequent_plain_pform interp (ts,(form,form2)) hash rs1 rs2 : representative pform * representative pform =
  let rs1 = (*Rset.union *)(rv_trans_set rs1) (*(accessible_rs ts)*) in 
  let rs2 = rv_trans_set rs2 in 
  (pform_ts_rs_left interp ts hash rs1 rs2) @ (form_to_plain_pform interp rs1 hash ts form)
  ,(pform_ts_rs_right interp ts hash rs1 rs2) @ (form_to_plain_pform interp rs1 hash ts form2)
  
   


let closes vs p = 
  match vs with 
    Plain_VS vm -> closes vm p
  | Fresh_VS _ -> true

