open Vars

exception Contradiction
exception No_match

exception Failed
exception Success


type fldlist = (string * args) list
and args = 
  | Arg_var of var
  | Arg_string of string
  | Arg_op of string * args list
  | Arg_record of (string * args) list

type pure =
  | EQ of args * args
  | NEQ of args * args
  | PPred of string * args list

type spatial =
  | SPred of string * args list 
  | Wand of form * form
  | Or of form * form 
  | Septract of form * form
  | Garbage
  | False

and form = pure list * spatial list


let conjunction (p1,s1) (p2,s2) = (p1@p2,s1@s2)

let disjunction (p1,s1) (p2,s2) = ([], [Or((p1,s1),(p2,s2))])

let wand (p1,s1) (p2,s2) = ([], [Wand((p1,s1),(p2,s2))])
  
let (&&&) = conjunction

let compare_arg a1 a2 =
  match a1, a2 with 
    Arg_var v1, Arg_var v2 -> compare_var v1 v2
  | _ -> compare a1 a2  



let mkNEQ(a1,a2) = 
  if compare_arg a1 a2 < 0 
  then NEQ(a1,a2) else NEQ(a2,a1)

let mkEQ(a1,a2) = 
  if compare_arg a1 a2 < 0 
  then EQ(a1,a2) else EQ(a2,a1)


(* Probably want to be careful so identifiers and strings are dealt with correctly *)
let compare_pure  ca1 ca2 = compare ca1 ca2
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



(* substitution *)
module IntMap =
  Map.Make(struct
    type t = var
    let compare = compare
  end)

module FreshVars = 
  Hashtbl.Make(struct 
    type t = var
    let equal = (=)
    let hash = Hashtbl.hash
  end)

type varmap = 
  | Plain of (args IntMap.t)
  | Freshen of (args IntMap.t) *  (args FreshVars.t)
  | ConcreteP of (var FreshVars.t)
  | ConcreteE of (var FreshVars.t)

(*type VarMap = int IntMap.t*)

let find key (map : varmap) = 
  match map with 
    Plain map -> IntMap.find key map  
  | Freshen (map,h) ->( 
      try IntMap.find key map 
      with Not_found -> 
	try FreshVars.find h key
	with Not_found -> 
	  let newvar = Arg_var (freshen key) in 
	  FreshVars.add h key newvar;
	  newvar
     )
  | ConcreteP h -> 
      Arg_var (try FreshVars.find h key    
      with Not_found ->      
	(match key with
	  EVar(a,b) -> 
	    (let newvar = (freshp_str("h" ^ b)) in
	    FreshVars.add h key newvar; newvar)
	| _ -> (FreshVars.add h key key); key))
  | ConcreteE h -> 
    Arg_var (try FreshVars.find h key    
      with Not_found ->      
	(match key with
	  PVar(a,b) -> 
	    (let newvar = freshe_str("n" ^ b) in
	    FreshVars.add h key newvar; newvar)
	| _ -> (FreshVars.add h key key); key))

 
let add (key : var)  (v : args)  (map : varmap) : varmap =
  match map with 
    Plain map -> Plain (IntMap.add key v map)
  | Freshen (map,h) -> Freshen((IntMap.add key v map),h)
  | ConcreteP h | ConcreteE h  -> assert false

let empty : varmap = Plain (IntMap.empty)

let varmapmap f (map : varmap) = 
  match map with 
    Plain v -> Plain (IntMap.map f v)
  | Freshen (v,h) -> Freshen (IntMap.map f v,h)
  | ConcreteP h | ConcreteE h  -> assert false

let is_empty  (vm : varmap) = 
  match vm with 
    Plain vm -> IntMap.is_empty vm
  | Freshen (vm,h) -> IntMap.is_empty vm
  | ConcreteP h | ConcreteE h  -> assert false

let freshening_subs subs : varmap =
    match subs with 
      Plain subs -> Freshen (subs, FreshVars.create 30 )
    | _ -> assert false

let concrete_subs () = ConcreteP (FreshVars.create 30)

let reverse_concrete subs = 
  match subs with
    ConcreteP h -> 
	let newh = FreshVars.create 30 in 
	FreshVars.iter (fun a b -> FreshVars.add newh b a) h; ConcreteE newh
  | _ -> assert false


(* substitution code for formula *)
let subst_var subs v = (try find v subs with Not_found -> Arg_var v)


let rec subst_args subs arg : args= 
  match arg with 
  | Arg_var v -> (subst_var subs v)
  | Arg_string s -> Arg_string s
  | Arg_op (name,args) -> Arg_op(name,List.map (subst_args subs) args)
  | Arg_record fldlist -> Arg_record (List.map (fun (f,v) -> f,subst_args subs v) fldlist)	
let subst_pure subs pa =
  match pa with 
   | EQ(a1,a2) -> mkEQ(subst_args subs  a1, subst_args subs a2)
   | NEQ (a1,a2) ->
   let a1,a2 = subst_args subs a1, subst_args subs a2 in 
   if a1=a2 then raise Contradiction else mkNEQ(a1,a2)
   | PPred(name,args) -> PPred (name,(List.map (subst_args subs) args))
     
let rec subst_spatial subs (sa : spatial) ((pform, sform) : form) : form=
  match sa with 
  | SPred(name,args) -> (pform, SPred(name,(List.map (subst_args subs) args)) :: sform)
  | Or (f1,f2) -> 
      (let f1 = try Some (subst_form subs f1)
      with Contradiction -> None in 
      let f2 = try Some (subst_form subs f2)
      with Contradiction -> None in
      match f1,f2 with 
      |	Some f1, Some f2 -> pform, Or(f1,f2) :: sform
      | Some (pf,sf), None 
      | None, Some (pf,sf) -> (pf @ pform), (sf @ sform) 
      | None, None -> raise Contradiction)
  | Wand (f1,f2) ->
      (let f1 = try Some (subst_form subs f1)
      with Contradiction -> None in 
      let f2 = try subst_form subs f2
      with Contradiction -> [],[False] in
      match f1 with 
      | Some f1 ->  pform, Wand(f1, f2) :: sform
      | None -> pform, Garbage :: sform)
  | Septract (f1,f2) ->
      pform,Septract (subst_form subs f1, subst_form subs f2)::sform
  | Garbage -> pform, Garbage::sform
  | False -> raise Contradiction 

and subst_form subs ((pform,sform):form) =
  let pform =   (List.map (subst_pure subs) pform) in
  let pform1,sform = 
    (List.fold_left 
       (fun form sa  -> subst_spatial subs sa form) 
       (([],[]):form) sform) in
  pform1 @ pform , sform 
  



(* pretty print *)
let rec string_varlist vl = 
  match vl with  
    [] -> ""
  | v::[] -> Printf.sprintf  "%s" (string_var v)
  | v::vl -> Printf.sprintf "%s,%s" (string_var v) (string_varlist vl)

let rec string_args a = 
  match a with 
    Arg_var v -> string_var v
  | Arg_string s -> Printf.sprintf "\"%s\"" s
  | Arg_op (s,al) -> Printf.sprintf "%s(%s)" s (string_arglist al) 
  | Arg_record fldlist -> Printf.sprintf "{ %s }" (string_fldlist fldlist)
and string_arglist al = 
  match al with  
    [] -> ""
  | a::[] -> Printf.sprintf  "%s" (string_args a)
  | a::al -> Printf.sprintf "%s,%s" (string_args a) (string_arglist al)
and string_fldlist fldlist = 
  match fldlist with
    [] -> ""
  | (f,v)::[] ->  Printf.sprintf  "%s=%s" f (string_args v)
  | (f,v)::al -> Printf.sprintf "%s=%s; %s" f (string_args v) (string_fldlist al)


let string_pure ca =  
  match ca with 
    NEQ(a1,a2) -> Printf.sprintf "%s != %s" (string_args a1)  (string_args a2)
  | EQ(a1,a2) -> Printf.sprintf "%s == %s" (string_args a1)  (string_args a2)
  | PPred(op,al) -> Printf.sprintf "%s(%s)" op (string_arglist al) 

let string_pure_list pl = 
  (String.concat " /\\ " (List.map string_pure pl))

let rec string_spatial s =
  match s with 
    SPred (s,al) -> Printf.sprintf "%s(%s)" s (string_arglist al)
  | Or(f1,f2) -> Printf.sprintf "(%s) \\/ (%s)" (string_form f1) (string_form f2)
  | Wand(f1,f2) -> Printf.sprintf "(%s) -* (%s)" (string_form f1) (string_form f2)
  | Septract(f1,f2) -> Printf.sprintf "(%s) -o (%s)" (string_form f1) (string_form f2)
  | False -> Printf.sprintf "False"
  | Garbage -> Printf.sprintf "Garbage"

and string_spatial_list sl = 
    (String.concat " * " (List.map string_spatial sl))

and string_spatial_list_nl sl = 
    (String.concat " *\n " (List.map string_spatial sl))

and string_form (pl,sl) = 
  Printf.sprintf "%s | %s"
    (string_pure_list pl)
    (string_spatial_list sl)

and string_form_nl (pl,sl) = 
  Printf.sprintf "%s |\n %s"
    (string_pure_list pl)
    (string_spatial_list_nl sl)

    
let string_seq (f,l,r) = 
  Printf.sprintf  "%s  |  %s  |-  %s" 
    (String.concat " * " (List.map string_spatial f))
    (string_form l)
    (string_form r)



module VarSet =
  Set.Make(struct
    type t = var
    let compare = compare
  end)

let rec fv_args args set = 
  match args with
    Arg_var var -> VarSet.add var set 
  | Arg_string _ -> set
  | Arg_op (name,argsl) -> fv_args_list argsl set
  | Arg_record fldlist -> fv_fld_list fldlist set
and fv_args_list argsl set =
  match argsl with 
    [] -> set
  | args::argsl -> fv_args_list argsl (fv_args args set)
and fv_fld_list fldlist set =
  match fldlist with
    [] -> set
  | (f,args)::fldlist -> fv_fld_list fldlist (fv_args args set)
    
let fv_pure pure set =
  match pure with
    EQ(x,y) -> fv_args x (fv_args y set)
  | NEQ(x,y) -> fv_args x (fv_args y set)
  | PPred(name, argsl) -> fv_args_list argsl set

let rec fv_pure_list pl set = 
  match pl with 
    [] -> set
  | p::pl -> fv_pure_list pl (fv_pure p set)

let rec fv_spat spat set = 
  match spat with
  | SPred(name, argsl) -> fv_args_list argsl set
  | Wand(f1,f2) 
  | Septract(f1,f2) 
  | Or(f1,f2) -> fv_form f1 (fv_form f2 set)
  | Garbage 
  | False -> set
and fv_spat_list sl set = 
  match sl with 
    [] -> set
  | s::sl -> fv_spat_list sl (fv_spat s set)
and fv_form (pl,sl) set =
 fv_spat_list sl (fv_pure_list pl set)


let rec ev_args args set = 
  match args with
    Arg_var var -> (match var with EVar _ -> VarSet.add var set | _ -> set )
  | Arg_string _ -> set
  | Arg_op (name,argsl) -> ev_args_list argsl set
  | Arg_record fldlist -> ev_fld_list fldlist set
and ev_args_list argsl set =
  match argsl with 
    [] -> set
  | args::argsl -> ev_args_list argsl (ev_args args set)
and ev_fld_list fldlist set =
  match fldlist with
    [] -> set
  | (f,args)::fldlist -> ev_fld_list fldlist (ev_args args set)
    
let ev_pure pure set =
  match pure with
    EQ(x,y) -> ev_args x (ev_args y set)
  | NEQ(x,y) -> ev_args x (ev_args y set)
  | PPred(name, argsl) -> ev_args_list argsl set

let rec ev_pure_list pl set = 
  match pl with 
    [] -> set
  | p::pl -> ev_pure_list pl (ev_pure p set)

let rec ev_spat spat set = 
  match spat with
  | SPred(name, argsl) -> ev_args_list argsl set
  | Wand(f1,f2) 
  | Septract(f1,f2) 
  | Or(f1,f2) -> ev_form f1 (ev_form f2 set)
  | Garbage 
  | False -> set
and ev_spat_list sl set = 
  match sl with 
    [] -> set
  | s::sl -> ev_spat_list sl (ev_spat s set)
and ev_form (pl,sl) set =
 ev_spat_list sl (ev_pure_list pl set)


let subst_kill_vars_to_fresh_prog vars =
  Plain (VarSet.fold (fun ev vm -> IntMap.add  ev (Arg_var (freshp())) vm) vars IntMap.empty)

let subst_kill_vars_to_fresh_exist vars =
  Plain (VarSet.fold (fun ev vm -> IntMap.add  ev (Arg_var (freshe())) vm) vars IntMap.empty)


(* Second type of axiom *)

(* frame, P,S |- P',S' *)
type sequent = spatial list * form * form

type varterm = 
    Var of VarSet.t
  | EV of args

type where = 
  | NotInContext of varterm
  | NotInTerm of varterm * args

(* if sequent matches, then replace with each thing  in the sequent list *)
type sequent_rule = sequent * (sequent list list) * string * (pure list) * (where list)

let string_rule (rule :sequent_rule ) =
  match rule with
    (conc, prem_s_s, name, without, where) ->
      string_seq conc
	

let mk_seq_rule (mat_seq,premises,name) = 
  mat_seq,premises,name,[],[]

type emp_rule = spatial * (pure list) * string

type pure_rule = spatial list * pure list list * string

type rewrite_rule = string * args list * args * (pure list) * (where list) * (pure list) (* if *) * string

type rules = 
  | SeqRule of sequent_rule
  | EmpRule of emp_rule
  | PureRule of pure_rule
  | RewriteRule of rewrite_rule
  | PredPrecise of string * bool list * string

type rewrite_entry =  (args list * args * (pure list) * (where list) * (pure list) * string ) list

(* substitution *)
module RewriteMap =
  Map.Make(struct
    type t = string
    let compare = compare
  end)

type rewrite_map =  rewrite_entry RewriteMap.t 

(* rules for simplifying septraction need defining as well *)


(* subst on a sequent *)

(* consider contradiction on right and left *)
let subst_sequent subs seq =
  match seq with
    framed,(pure,leftseq),(pureright,rightseq) ->
      let pf,sf = try subst_form subs ([],framed) with Contradiction -> raise Success in 
      let pl,sl = try subst_form subs (pure,leftseq) with Contradiction -> raise Success in 
      let pr,sr = try subst_form subs (pureright, rightseq) with Contradiction -> ([],[False]) in 
      (sf, (pf @ pl, sl), (pr, sr))
    
let sequent_join seq1 seq2 =
  match seq1,seq2 with
    (framed1,(pure1,leftseq1),(pureright1,rightseq1)),
    (framed2,(pure2,leftseq2),(pureright2,rightseq2))
    -> (framed1@framed2,(pure1@pure2,leftseq1@leftseq2),(pureright1@pureright2,rightseq1@rightseq2))


type logic = sequent_rule list *  emp_rule list * pure_rule list * rewrite_map

let empty_logic = [],[],[],RewriteMap.empty 

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
	    (fn,a,b,c,d,e,f) -> (sl,el,pl,RewriteMap.add fn ((a,b,c,d,e,f)::(try RewriteMap.find fn rm with Not_found -> [])) rm))
  in rule_list_to_logic_inner rl 

type question =
  |  Implication of form * form 
  |  Inconsistency of form
  |  Frame of form * form
  |  Equal of form * args * args
  |  Abs of form 



