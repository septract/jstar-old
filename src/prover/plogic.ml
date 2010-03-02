open Debug
open Vars
open Pterm
open Jimple_global_types


type pform_at = plogic_pform_at


type pform = plogic_pform


let mkFalse = [P_False]

let isFalse f =
  match f with 
    [P_False] -> true 
  | _ -> false

let pconjunction (f1 : pform)  (f2 : pform) : pform = 
 if isFalse f1 then f1 else if isFalse f2 then f2 else f1 @ f2

let (&&&) = pconjunction


let pwand f1 f2 = [P_Wand(f1,f2)]

let mkNEQ(a1,a2) = [P_NEQ(a1,a2)]

let mkEQ(a1,a2) = [P_EQ(a1,a2)]

let mkPPred(n,al) = [P_PPred(n,al)]
let mkSPred(n,al) = [P_SPred(n,al)]

let mkGarbage = [P_Garbage]

let mkOr(f1,f2) = 
  if isFalse f1 then f2 
  else if isFalse f2 then f1 
  else [P_Or(f1,f2)]

let mkWand(f1,f2) = 
  if isFalse f1 then 
    mkGarbage
  else [P_Wand(f1,f2)]

let mkSeptract(f1,f2) = 
  if isFalse f1 then f1 
  else if isFalse f2 then f2 
  else [P_Septract(f1,f2)]

let mkEmpty = []


let rec subst_pform_at subs pa=
  match pa with 
   | P_EQ(a1,a2) -> mkEQ(subst_args subs  a1, subst_args subs a2)
   | P_NEQ (a1,a2) ->
       let a1,a2 = subst_args subs a1, subst_args subs a2 in 
       (*if a1=a2 then mkFalse else*) mkNEQ(a1,a2)
   | P_PPred(name,args) -> mkPPred(name,(List.map (subst_args subs) args))
   | P_SPred(name,args) -> mkSPred(name,(List.map (subst_args subs) args))
   | P_Or (f1,f2) -> mkOr(subst_pform subs f1,subst_pform subs f2)
   | P_Wand (f1,f2) -> mkWand(subst_pform subs f1,subst_pform subs f2)
   | P_Septract (f1,f2) -> mkSeptract(subst_pform subs f1,subst_pform subs f2)
   | P_Garbage -> mkGarbage 
   | P_False -> mkFalse
and subst_pform subs = 
    List.fold_left (fun pf pa -> (subst_pform_at subs pa) &&& pf) []
  



(* pretty print *)
let rec string_varlist vl = 
  match vl with  
    [] -> ""
  | v::[] -> Printf.sprintf  "%s" (string_var v)
  | v::vl -> Printf.sprintf "%s,%s" (string_var v) (string_varlist vl)

let rec list_format sep f ppf list = 
  match list with 
    [] -> Format.fprintf ppf ""
  | [x] -> Format.fprintf ppf "%a" f x 
  | x::xs -> Format.fprintf ppf "%a%s@ %a" f x sep (list_format sep f) xs 

let rec string_form_at ppf pa =  
  match pa with 
    P_NEQ(a1,a2) -> Format.fprintf ppf "%a != %a" string_args a1  string_args a2
  | P_EQ(a1,a2) -> Format.fprintf ppf "%a = %a" string_args a1  string_args a2
  | P_PPred(op,al) -> Format.fprintf ppf "%s(%a)" op string_args_list al
  | P_SPred (s,al) -> Format.fprintf ppf "%s(%a)" s string_args_list al
  | P_Or(f1,f2) -> Format.fprintf ppf "@[@[(%a)@] || @[(%a)@]@]" string_form f1 string_form f2
  | P_Wand(f1,f2) -> Format.fprintf ppf "@[@[(%a)@] -* @[(%a)@]@]" string_form f1  string_form f2
  | P_Septract(f1,f2) -> Format.fprintf ppf "@[@[(%a)@] -o @[(%a)@]@]" string_form f1  string_form f2
  | P_False -> Format.fprintf ppf "False"
  | P_Garbage -> Format.fprintf ppf "Garbage"
and string_form ppf pf = 
  Debug.list_format "*" string_form_at ppf pf 





let rec fv_form_at pa set =
  match pa with
    P_EQ(x,y) -> fv_args x (fv_args y set)
  | P_NEQ(x,y) -> fv_args x (fv_args y set)
  | P_PPred(name, argsl) -> fv_args_list argsl set
  | P_SPred(name, argsl) -> fv_args_list argsl set
  | P_Wand(f1,f2) 
  | P_Septract(f1,f2) 
  | P_Or(f1,f2) -> fv_form f1 (fv_form f2 set)
  | P_Garbage 
  | P_False -> set
and fv_form pf set =
 List.fold_left (fun set pa -> fv_form_at pa set) set pf 


let closes subs p  = 
  not (vs_exists (fun x -> not (vm_mem x subs)) (fv_form p vs_empty))


    
let rec ev_form_at pa set =
  match pa with
    P_EQ(x,y) -> ev_args x (ev_args y set)
  | P_NEQ(x,y) -> ev_args x (ev_args y set)
  | P_PPred(name, argsl) -> ev_args_list argsl set
  | P_SPred(name, argsl) -> ev_args_list argsl set
  | P_Wand(f1,f2) 
  | P_Septract(f1,f2) 
  | P_Or(f1,f2) -> ev_form f1 (ev_form f2 set)
  | P_Garbage 
  | P_False -> set
and ev_form pf set =
 List.fold_left (fun set pa -> ev_form_at pa set) set pf  

type psequent = pform * pform * pform


let fv_psequent (pff,pfl,pfr) = 
  (fv_form pff (fv_form pfl (fv_form pfr vs_empty)))

let subst_psequent subst (pff,pfl,pfr) = 
  (subst_pform subst pff, subst_pform subst pfl, subst_pform subst pfr)



let purify pal = 
  List.map (
    fun x -> 
      match x with 
	P_EQ(_,_) | P_NEQ(_,_) -> x 
      |	P_SPred(n,al) -> P_PPred(n,al)
      |	_ -> unsupported ()
	    ) pal
