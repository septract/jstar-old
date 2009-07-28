(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)



(************************************************************
  I think this uses something like Shostak's algorithm for
  equalities.
*************************************************************)
open Debug
open Pterm
open Plogic
open Printf 
exception Contradiction
exception No_match

exception Failed
exception Success

let ts_debug=true
let ts_debug=false



let map_option f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el  with
	None -> rest
   |	Some el -> el::rest) l []

let map_lift_exists f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el, rest  with
	None,_ -> rest
   |	Some el,Some rest -> Some (el::rest)
   |  Some el, None -> Some [el]) l None

let map_lift_forall f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el, rest  with
     	  None,_ -> None
	    | _, None -> None
      |	Some el,Some rest -> Some (el::rest)) l (Some [])


type ('a,'b) sum = 
    Inr of 'a
  | Inl of 'b

let map_sum f l
    =
  List.fold_right
    (fun el (restl,restr) -> 
      match f el with
      | Inl l -> (l::restl,restr)
      | Inr r -> (restl,r::restr)) l ([],[])

(* Representation for equality: congruence closed *)

(* Need to add way of adding rewrite rules *)

(***************************************************
 *
 *   Flattened terms for efficient representation 
 *   of terms
 * 
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
    mutable term : flattened_term;
    mutable rep : representative;
    nn : int;
   }
    
(*************
 *  Term constructor
 ************)
let tcount = ref 0
let next_tcount () = 
  tcount := !tcount+1;
  !tcount

let new_term rep ft redun : term =
  ref {rep=rep;term=ft;nn=next_tcount(); redundant=redun}  

(***********************************************
 *  Ugly printer
 ***********************************************)

let string_rep_db ppf (r : representative) = 
  Format.fprintf ppf "%s_%d%s" (!r).name (!r).n (if (!r).deleted then "_deleted" else "")   

let rec string_rep_list_db ppf (rl : representative list) = 
  Debug.list_format "," string_rep_db ppf rl

let rec string_rep_fldlist_db ppf fld = 
  Debug.list_format ";" (fun ppf (f,r) -> Format.fprintf ppf "%s=%a" f  string_rep_db r) ppf fld

let string_ft_db ppf ft : unit = 
  match ft with 
    FTConstr (name,rl) ->  
      Format.fprintf ppf "%s(%a)" name string_rep_list_db rl
  | FTFunct (name,rl) -> 
      Format.fprintf ppf "%s(%a)" name string_rep_list_db rl
  | FTRecord fld_list -> 
      Format.fprintf ppf "@[{%a}@]" string_rep_fldlist_db fld_list
  | FTString s -> Format.fprintf ppf "\"%s\"" s 
  | FTPVar v -> Format.fprintf ppf "%s" (Vars.string_var v)


let ft_hash ft : int = 
  Hashtbl.hash ( 
  let f = (fun x-> Printf.sprintf "%d" (!x).n) in 
  match ft with 
    FTConstr (name,rl) ->  
      let rl = String.concat ", " (List.map f rl) in 
      Printf.sprintf "%s(%s)" name rl
  | FTFunct (name,rl) -> 
      let rl = String.concat ", " (List.map f rl) in 
      Printf.sprintf "%s(%s)" name rl
  | FTRecord fld_list -> 
      let fl,rl = List.split fld_list in 
      let rl = List.map f rl  in 
      let frl = List.map (fun (x,y) -> Printf.sprintf "%s=%s" x y) (List.combine fl rl) in
      "{" ^ (String.concat "; " frl)  ^ "}"
  | FTString s -> "\"" ^ s ^ "\"" 
  | FTPVar v -> Vars.string_var v
 )
  
(************************************************
 *
 *  Representitives
 *
 ************************************************)

let rep_eq (r1 : representative) (r2 : representative) = r1 == r2

let ft_eq ft1 ft2 = 
  match ft1,ft2 with 
  | FTConstr(n,rl), FTConstr(n2,rl2) -> 
      if n=n2 then (try List.for_all2 rep_eq rl rl2 with Invalid_argument _ -> false) else false
  | FTFunct(n,rl), FTFunct(n2,rl2) -> 
      if n=n2 then (try List.for_all2 rep_eq rl rl2 with Invalid_argument _ -> false) else false
  | FTRecord(frl), FTRecord(frl2) ->  
      let fl,rl = List.split frl in 
      let fl2,rl2 = List.split frl2 in 
      if fl=fl2 then 
	(try 
	  List.for_all2 rep_eq rl rl2 
	with Invalid_argument _ -> 
	  if ts_debug then 
	    (Format.fprintf !dump   "Failed comp: %a %a\n"  string_ft_db ft1    string_ft_db ft2); 
	  false) 
      else 
	(if ts_debug then Format.fprintf !dump   "Failed comp: %a @ %a\n" string_ft_db ft1 string_ft_db ft2; 
	 false)
  | FTString(s), FTString(s2) -> s=s2
  | FTPVar(v), FTPVar(v2) -> v=v2 
  | _,_ -> false

let current = ref 0

let next_rep() : representative = 
  let x = !current in current := x+1;
  if ts_debug then Format.fprintf !dump  "Created new rep: r_%d@\n" x;
  ref { terms = [] ; uses = []; n=x; name="r" ; deleted = false} 

let rep_hash r1 = (!r1).n 

let rep_compare r1 r2 = 
  let n1 = (!r1).n in
  let n2 = (!r2).n in
  if n1 < n2 then 1 else if n1=n2 then 0 else -1

let t_compare r1 r2 = 
  let n1 = (!r1).nn in
  let n2 = (!r2).nn in
  if n1 < n2 then 1 else if n1=n2 then 0 else -1

(* Used as a canonical representative of a term *)
(*IF-OCAML*)
module Rhash = 
  Hashtbl.Make(struct 
    type t = representative
    let equal = rep_eq
    let hash = rep_hash
  end)
module Rhash_args = Rhash
module Rhash_args_opt = Rhash
type 'a rhash_t = 'a Rhash.t  
(*ENDIF-OCAML*)
(*F#
let Rhash = Hashtbl.Make(rep_hash,rep_eq)
let Rhash_args = Hashtbl.Make(rep_hash,rep_eq)
let Rhash_args_opt = Hashtbl.Make(rep_hash,rep_eq)
type 'a rhash_t = Tagged.HashMultiMap<representative,'a,System.Collections.Generic.IEqualityComparer<representative>>
F#*)

let rao_create () = (Rhash_args_opt.create 30)

(*IF-OCAML*)
module Rmap = 
  Map.Make(struct 
    type t = representative
    let compare = rep_compare
  end)
(*ENDIF-OCAML*)
(*
type rmap = representative Rmap.t
let rmap_empty () = Rmap.empty 
let rmap_find r map= Rmap.find r map  
let rmap_map f map =
  let map_copy = Rhash.copy map in
  Rhash.iter (fun r r' -> Rhash.replace map r (f r')) map_copy; map  
let rmap_mem r map = Rmap.mem r map
let rmap_add r1 r2 map = Rmap.add r1 r2 map
let rmap_printf map = Rmap.iter (fun r1 r2 -> Format.fprintf !dump  "Maps %s to %s\n" (string_rep r1) (string_rep r2)) map
*)

(*Removed the following as it breaks in F# due to the semantics of iterator:
  let rmap_map f map = Rmap.map f map*)

type rmap = representative rhash_t
let rmap_empty () = Rhash.create 20 
let rmap_find r map = Rhash.find map r
(*IF-OCAML*)
let rmap_map f map = Rhash.iter (fun r r' -> Rhash.replace map r (f r')) map; map
(*ENDIF-OCAML*)
(*F#
let rmap_map f map =
  let map_copy = Rhash.copy map in
  Rhash.iter (fun r r' -> Rhash.replace map r (f r')) map_copy; map  
F#*)

let rmap_mem r map = Rhash.mem map r  
let rmap_add r1 r2 map = Rhash.add map r1 r2; map 
let rmap_printf map = Rhash.iter (fun r1 r2 -> Format.fprintf !dump  "Maps %a to %a@n" string_rep_db r1 string_rep_db r2) map



(*IF-OCAML*)
module Rset = 
  Set.Make(struct 
    type t = representative
    let compare = rep_compare
  end)
type rset_t = Rset.t
(*ENDIF-OCAML*)

(*F#
type rset_t = Tagged.Set<representative,System.Collections.Generic.IComparer<representative>>
let Rset = Set.Make(rep_compare)
F#*)

(*
let string_rset rs = string_rlist (Rset.elements rs)
*)

(*IF-OCAML*)
module Thash = 
  Hashtbl.Make(struct 
    type t = flattened_term
    let equal = ft_eq
    let hash = ft_hash
  end)
type thash_t = representative Thash.t
(*ENDIF-OCAML*)

(*F#
let Thash : Hashtbl.Provider<flattened_term,representative> = Hashtbl.Make(ft_hash,ft_eq) 
type thash_t = Tagged.HashMultiMap<flattened_term,representative,System.Collections.Generic.IEqualityComparer<flattened_term>>
F#*)    

(* Structure for representing terms upto equality *)
type term_structure = 
    { termhash : thash_t;
      mutable repset : rset_t }

(*IF-OCAML*)
module TIDset = 
  Set.Make(struct 
    type t = term
    let compare = fun t1 t2 -> compare (!t1).nn (!t2).nn
  end)
(*ENDIF-OCAML*)

(*F#
let TIDset : Set.Provider<term> 
   = Set.Make(fun t1 t2 -> compare (!t1).nn (!t2).nn) 
F#*)    
  



let lift f x =
  match x with 
    Some x -> Some (f x)
  | None -> None 

let string_term ppf tid = 
    Format.fprintf ppf "%a of %a" string_ft_db (!tid).term  string_rep_db (!tid).rep 

let rec string_tlist ppf tl = 
  let f ppf tid = 
    Format.fprintf ppf "%a of %a" string_ft_db (!tid).term  string_rep_db (!tid).rep in
  match tl with 
    [] -> Format.fprintf ppf ""
  | [t] -> f ppf t
  | t::tl -> Format.fprintf ppf "%a,%a" f t string_tlist tl


(* Convert reps to terms *)
(* Assumes acyclic for now *)
let rec rep_to_args r hash : (( representative args * (term option)) ) = 
  try Rhash_args_opt.find hash r 
  with Not_found -> 
    Rhash_args_opt.add hash r (Arg_hole r, None);
    let term_ref = 
      try Some (List.find (fun x -> match !x.term with FTPVar _ | FTFunct(_,[]) -> true | _ -> false) (!r).terms) 
      with Not_found -> 
	try  Some (List.find (fun x -> true ) (!r).terms)  
	with Not_found -> None  in 
    (*List.tryfind (fun t -> match term_to_args (!t).term hash with Some _ -> true | _ -> false) ((!r).terms) in*)
    match term_ref with
      Some term_ref -> 
        let args = term_to_args (!term_ref).term hash in 
        Rhash_args_opt.replace hash r (args, Some term_ref);
        (args, Some term_ref)
    | _ -> (Arg_hole r, None)
and term_to_args term hash : (representative args) =
  match term with 
    FTConstr (name,rl) ->  
      let al = List.map (fun r -> fst (rep_to_args r hash)) rl in
      Arg_cons(name,al)  
  | FTFunct (name,rl) -> 
      let al = List.map (fun r -> fst (rep_to_args r hash)) rl in
      Arg_op(name,al)  
  | FTRecord fld_list -> 
      let fl,rl = List.split fld_list in 
      let al = List.map (fun r -> fst (rep_to_args r hash)) rl in
      Arg_record (List.combine fl al)

(*    FTConstr (name,rl) ->  
      let al_opt = map_lift_forall (fun r -> fst (rep_to_args r hash)) rl in
      lift (fun x -> Arg_cons(name,x)) al_opt  
  | FTFunct (name,rl) -> 
      let al_opt = map_lift_forall (fun r -> fst (rep_to_args r hash)) rl in
      lift (fun x -> Arg_op(name,x)) al_opt  
  | FTRecord fld_list -> 
      let fl,rl = List.split fld_list in 
      let al_opt = map_lift_forall (fun r -> lift fst (rep_to_args r hash)) rl in
      lift Arg_record (lift (List.zip fl) al_opt)*)
  | FTString s -> Arg_string s
  | FTPVar v -> Arg_var v


(***********************************************
 *  Less Ugly printer
 ***********************************************)

(*
let string_rep_2 (r : representative) = 
  let term_list = (!r).terms in 
  if ts_debug then (Printf.sprintf "%s_%d" (!r).name (!r).n ), None 
  else
  try 
    let term_name = List.find (fun x -> match (!x).term with FTString(s) -> true | FTPVar(s) -> true  | FTFunct(n,[]) -> true | _ -> false) term_list in  
    (match (!term_name).term with 
    | FTString s -> "\"" ^ s ^ "\"" 
    | FTPVar v -> Vars.string_var v
    | FTFunct (n,[]) -> n ^ "()"
    | _ -> unsupported ()), Some term_name
  with Not_found -> 
	(Printf.sprintf "%s_%d" (!r).name (!r).n ), None  *)

let string_rep hash ppf (r : representative) = 
  if ts_debug then (Format.fprintf ppf "%s_%d" (!r).name (!r).n )
  else
  let f = rep_to_args r hash in  
  match f with 
   args, _ -> string_args_hole string_rep_db ppf args
 
(* let string_rep (r : representative) : string  = fst(string_rep_2 r) *)

let rec string_rlist hash ppf vl = 
  Debug.list_format "," (string_rep hash) ppf vl

 
let string_ft hash ppf ft  = 
  match ft with 
    FTConstr (name,rl) ->  
      Format.fprintf ppf "%s(%a)" name (Debug.list_format "," (string_rep hash)) rl  
  | FTFunct (name,rl) -> 
      Printf.printf "Printing: %s\n" name;
      (match name,rl with
	"builtin_plus", [r1;r2] -> Format.fprintf ppf "(%a + %a)" (string_rep hash) r1 (string_rep hash) r2
      | _ -> Format.fprintf ppf "%s(%a)" name (Debug.list_format "," (string_rep hash)) rl  )
  | FTRecord fld_list -> 
      Format.fprintf ppf "@[{%a}@]" (Debug.list_format ";" (fun ppf (f,a) -> Format.fprintf ppf "%s=%a" f (string_rep hash) a)) fld_list  
  | FTString s -> Format.fprintf ppf "\"%s\"" s 
  | FTPVar v -> Format.fprintf ppf "%s" (Vars.string_var v)


let print_termhash ts = 
  Thash.iter (
  fun term rep ->
    Format.fprintf !dump  "@ @ @[%a,%a@]@\n" string_ft_db term string_rep_db rep;
 ) ts.termhash



  
  
(****************************************
    Representatives calculation
 ****************************************)
let rv_ft ft rs : rset_t = 
  match ft with 
    FTConstr (name,rl) ->  
      List.fold_left (fun rs r-> Rset.add r rs) rs rl
  | FTFunct (name,rl) -> 
      List.fold_left (fun rs r-> Rset.add r rs) rs rl
  | FTRecord fld_list -> 
      let fl,rl = List.split fld_list in 
      List.fold_left (fun rs r-> Rset.add r rs) rs rl
  | FTString s -> rs
  | FTPVar v -> rs

let rv_fts fts (rs :rset_t)  : rset_t = 
  List.fold_left (fun rs ft -> rv_ft ft rs) rs fts 

let rec rv_transitive_set_fb fb (r : representative) (rs : rset_t) : rset_t =
  let rec rv_inner r rs = 
    if Rset.mem r rs then rs else
    try 
      let rs = Rset.add r rs in 
      let term_refs = (!r).terms in 
      let rs = List.fold_left (fun rs tref -> if TIDset.mem tref fb then rs else rv_ft_trans (!tref).term rs) rs term_refs in
      rs 
    with Not_found -> rs
  and rv_ft_trans ft rs : rset_t =
    match ft with 
      FTConstr (name,rl) ->  
	List.fold_left (fun rs r-> rv_inner r rs) rs rl
    | FTFunct (name,rl) -> 
	List.fold_left (fun rs r-> rv_inner r rs) rs rl
    | FTRecord fld_list -> 
	let fl,rl = List.split fld_list in 
      List.fold_left (fun rs r-> rv_inner r rs) rs rl
    | FTString s -> rs
    | FTPVar v -> rs
  in rv_inner r rs

let rec rv_transitive_set (r : representative) (rs : rset_t) : rset_t =
  rv_transitive_set_fb TIDset.empty r rs 


let rv_transitive r = 
  try 
    rv_transitive_set r Rset.empty
  with Not_found -> unsupported ()
	  
let rv_trans_set rs : rset_t =
  try 
    Rset.fold (fun r rs -> rv_transitive_set r rs) rs Rset.empty
  with Not_found -> unsupported () 

let accessible_rs_fb forbidden ts =
  Thash.fold 
    (fun term rep rs -> 
      if (!rep).deleted then rs else  
      match term with 
	FTPVar(Vars.PVar(i,v)) -> (*if i=0 then *) rv_transitive_set_fb  forbidden rep rs (*else rs*)
      | _ -> if List.length ((!rep).terms) > 1 then rv_transitive_set_fb forbidden rep rs else rs
    ) ts.termhash Rset.empty (*ts.repset*)


let accessible_rs ts =
  accessible_rs_fb TIDset.empty ts


(******************************* 
   More pretty printer 
 ********************************)
let string_term_args hash ppf (terms,args) = 
  match terms with 
  | [] -> Format.fprintf ppf "%a" (string_args_hole string_rep_db) args 
  | _ -> Format.fprintf ppf
	"@[%a@ = %a@ @]@ " 
	(string_args_hole string_rep_db) args 
	(Debug.list_format " =" 
	   (fun ppf t -> string_args_hole string_rep_db ppf (term_to_args (!t).term hash))
	   ) terms

let rep_to_terms_args hash r = 
    match rep_to_args r hash with 
      args,None -> (!r).terms,args  
    | args,Some term -> List.filter (fun t -> t != term) (!r).terms, args

let string_rep_term hash ppf r = 
  let terms,args = rep_to_terms_args hash r in 
  string_term_args hash ppf (terms,args)

(*	)) ^ " * \n" ) *)


let string_rep_term_db ppf r = 
  Format.fprintf ppf "@[%a =@ %a@]"  string_rep_db r (Debug.list_format "=" (fun ppf t -> string_ft_db ppf (!t).term)) (!r).terms 

let rset_to_list rs = Rset.fold (fun r rl -> r::rl) rs []

let string_ts_inner rs hash ppf ts = 
  let rl = rset_to_list rs in 
  let tal = List.map (rep_to_terms_args hash) rl in 
  let tal = List.filter (fun (t,a) -> List.length t>0) tal in 
  Debug.list_format "*" (string_term_args hash) ppf tal


let string_ts_inner_db rs ppf ts= 
  let rl = List.filter (fun r -> List.length (!r).terms>0) (rset_to_list rs) in 
  Debug.list_format " *" string_rep_term_db ppf rl


let printf_thash ppf ts = 
	       Thash.iter (
	       fun term rep ->
		 Format.fprintf ppf "  @[%a,%a@]\n" string_ft_db term string_rep_db rep;
	      ) ts.termhash

let string_ts_rs rs hash ppf ts= 
  let rs = Rset.union (rv_trans_set rs) (accessible_rs ts) in 
  string_ts_inner rs hash ppf ts

let string_ts hash ppf ts =
  let rs = accessible_rs ts in 
  string_ts_inner rs hash ppf ts

let string_ts_db ppf ts =
  let rs = accessible_rs ts in 
  string_ts_inner_db rs ppf ts


(************************************************
 Convert to pterm
 ************************************************)
let pterm_rep_2 interp rs (r : representative) : representative args * (term option) = 
  let term_list = (!r).terms in 
  try 
    let term_name = List.find (fun x -> match (!x).term with FTString(s) -> true | FTPVar(s) -> true  | FTFunct(n,[]) -> true | _ -> false) term_list in  
    (match (!term_name).term with 
    | FTString s -> Arg_string s  
    | FTPVar v -> Arg_var v
    | FTFunct (n,[]) -> Arg_op(n,[])
    | _ -> unsupported ()), Some term_name
  with Not_found -> 
	  try Rhash_args.find interp r, None 
	  with Not_found -> 
	    let var = Arg_var (if Rset.mem r rs then (Vars.freshp_str (toString string_rep_db r)) 
	                                        else (Vars.freshe_str (toString string_rep_db r))) in 
	    Rhash_args.add interp r var;
	    var,  None 


let rep_hole interp rs r = 
    try Rhash_args.find interp r
	  with Not_found -> 
	    (let var = Arg_var (if Rset.mem r rs then (Vars.freshp_str (toString string_rep_db r)) 
	                                        else (Vars.freshe_str (toString string_rep_db r))) in 
	    Rhash_args.add interp r var;
	    var)

let pterm_rep interp rs hash (r : representative) : representative args = 
  hole_replace (rep_hole interp rs) (fst (rep_to_args r hash))

(*
let pterm_rep interp rs x  =
   let ret = fst (pterm_rep_2 interp rs x ) in
   ret 
  *)
   
let rec pterm_rlist interp rs hash vl = 
  (List.map (pterm_rep interp rs hash) vl)

let pterm_ft interp rs hash ft : representative args = 
  match ft with 
    FTConstr (name,rl) ->  unsupported () (* unimplemented *)
  | FTFunct (name,rl) -> Arg_op(name, pterm_rlist interp rs hash rl)
  | FTRecord fld_list ->  unsupported () (* unimplemented *)
  | FTString s -> Arg_string s  
  | FTPVar v -> Arg_var v
  

(*******************************************************
  termstructure to pform 
 *******************************************************)
 let pform_rep_term interp rs hash r = 
  if ts_debug then Format.fprintf !dump  "Equals for %a\n" string_rep_db r;
  let args,r1 = rep_to_args r hash in
  let args = hole_replace (rep_hole interp rs) args in  
  let rterms = match r1 with Some r1 -> List.filter (fun t -> t != r1) (!r).terms | None -> (!r).terms in 
  match rterms,r1 with 
  | [],_ ->  []
  | _ -> 
	List.map 
	  (fun t -> 
        if ts_debug then Format.fprintf !dump  "   =%a\n" string_ft_db (!t).term;
	      Plogic.P_EQ (args,(pterm_ft interp rs hash ((!t).term)))
	   ) rterms

(*  rs1 is the representatives that should have equalities output
    rs2 is the representatives that should not be existentials. *)
let pform_ts_inner interp ts hash rs1 rs2 = 
  (Rset.fold 
     (fun rep sl -> 
	 (pform_rep_term interp rs2 hash rep) @ sl)
       rs1 []
  )
  
(*  rs1 is representatives on left hand side
    rs2 is representatives on right hand side. *)
let pform_ts_rs_left interp ts hash rs1 rs2 = 
  (*if ts_debug then Printf.printf "Left side contains %d elements: %s\n" (Rset.cardinal rs1) (string_rset rs1);*)
   pform_ts_inner interp ts hash rs1 rs1

(*  rs1 is representatives on left hand side
    rs2 is representatives on right hand side. *)
let pform_ts_rs_right interp ts hash rs1 rs2 = 
(*  (*if ts_debug then*) Printf.printf "Right side contains %d elements: %s\n" (Rset.cardinal rs2) (string_rset rs2);*)
  let rs2 = Rset.diff rs2 rs1 in (* ignores ones output on left *) 
  pform_ts_inner interp ts hash rs2 rs1
  

(* Allows the addition of representative with no associated term *)
let add_existential (ts: term_structure) : representative = 
  let rep_id = next_rep() in 
  ts.repset <- Rset.add rep_id ts.repset;
  rep_id  

let is_existential (ts: term_structure) (r : representative) : bool = 
  List.for_all 
    (fun tref -> 
      match (!tref).term with 
	FTPVar (Vars.EVar (_,_)) -> true
      | _ -> false 
    )
    (!r).terms
(*  try 
    match (!r).terms with 
      [] -> true
    | [tref] -> 
	(try
	  match (!tref).term with
	    FTPVar (Vars.EVar (_,_)) -> true
	  | _ -> false
	with Not_found -> unsupported ())	  
    | _ -> false
  with Not_found -> Printf.printf "Failed to find %s in \n %s\n" (string_rep r) (string_ts ts); unsupported () 
*)


(*   substitution stuff *)
(*type varhashrep = representative VarHash.t*)
type varhashrep = representative Pterm.varhash_t

type varmaprep = representative Pterm.varmap_t

type var_subst = 
    Plain_VS of varmaprep 
  | Fresh_VS of varmaprep * varhashrep
 
let empty_vs : var_subst = Plain_VS vm_empty

let find_vs ts key (map : var_subst) = 
  match map with 
    Plain_VS map -> vm_find key map  
  | Fresh_VS (map,h) ->( 
      try vm_find key map 
      with Not_found -> 
	try vh_find h key
	with Not_found -> 
	  let newvar = add_existential ts  in 
	  vh_add h key newvar;
	  newvar
     )

let add_vs (key : Vars.var)  v   (map : var_subst) : var_subst =
  match map with 
    Plain_VS map -> Plain_VS (vm_add key v map)
  | Fresh_VS (map,h) -> Fresh_VS ((vm_add key v map),h)


let freshening_vs subs : var_subst =
    match subs with 
      Plain_VS subs -> Fresh_VS (subs, vh_create 30 )
    | _ -> unsupported ()





let add_flat_term (ts : term_structure) (ft : flattened_term) 
    (sub_uses : representative list) (redun : bool)
    : representative * (term, flattened_term) sum =
  try 
    let rid = Thash.find ts.termhash ft in 
    rid, Inl ft
  with Not_found ->
    if ts_debug then Format.fprintf !dump  "Adding term %a.\n" string_ft_db ft;
    let rep_id = next_rep() in
    ts.repset <- Rset.add rep_id ts.repset;
    let term_id = new_term rep_id ft redun in
    (!rep_id).terms <- [term_id];
    assert(not(Thash.mem ts.termhash ft));
    Thash.add ts.termhash ft rep_id;
    List.iter (fun r -> (!r).uses <- (term_id::((!r).uses))) sub_uses;      
    if ts_debug then Format.fprintf !dump  "Added term: %a\n" string_ts_db ts;
    rep_id, Inr term_id

let map_lift f l s=
  List.fold_right
    (fun t (rl,interp) -> 
      let r,interp = f interp t in
      r::rl,interp
    ) l ([],s)

(* Returns new term structure and representative, 
   with the representative bound to a flattened version of t *) 
let rec add_term_id (ts : term_structure) (interp : var_subst) 
   (t : representative args) (redun : bool) : representative * var_subst * (term,flattened_term) sum option  = 
  let f ((rid,tid),interp) = rid,interp, Some tid in 
  match t with 
  | Arg_var v ->
      (try 
        let rid = find_vs ts v interp in 
        rid, interp, None
      with Not_found -> 
	(match v with 
	  Vars.PVar _ 
	| Vars.EVar _ -> let rid,tid = add_flat_term ts (FTPVar v) [] redun in 
	                 rid,interp,Some tid
        | Vars.AnyVar _  -> let rid = add_existential ts in (rid, add_vs v rid interp, None) 
	| _ -> unsupported ()
      ))	    
  | Arg_string s ->  f( add_flat_term ts (FTString s) [] redun, interp)
  | Arg_op (name, al) -> let rl,interp = add_terms ts interp al redun in f(add_flat_term ts (FTFunct(name, rl)) rl redun,interp)
  | Arg_cons (name, al) -> let rl,interp = add_terms ts interp al redun in f(add_flat_term ts (FTConstr(name, rl)) rl redun,interp)
  | Arg_record fld_list -> 
      let fl,al = List.split fld_list in 
      let rl,interp = add_terms ts interp al redun in 
      let fld_list = List.combine fl rl in 
      f(add_flat_term ts (FTRecord fld_list) rl redun, interp)
and add_term ts interp t redun = let rid,interp,tid = add_term_id ts interp t redun in (rid,interp)
and add_terms (ts : term_structure) (interp : var_subst) (tl : (representative args) list) (redun : bool) : representative list * var_subst =  
  map_lift (fun x y -> add_term ts x y redun) tl interp
(*
List.fold_left
    (fun (rl,interp) t -> 
      let r,interp = add_term ts interp t in
      r::rl,interp
    ) ([],interp) tl
*)
 

(* Lookup a term in term structure. Throws Not_found if it isn't known *)
let rec find_term_id (ts: term_structure) (t: 'a args) (interp : var_subst): representative * term option =
  let r,ft = match t with 
  | Arg_var v ->
      (try 
        find_vs ts v interp, None
      with Not_found -> 
	(match v with 
	  Vars.PVar _ -> Thash.find ts.termhash (FTPVar v), Some (FTPVar v)
  | Vars.EVar _ -> Thash.find ts.termhash (FTPVar v), Some (FTPVar v)
	| _ -> unsupported ()
      ))	     
  | Arg_string s ->  Thash.find ts.termhash (FTString s), Some (FTString s)
  | Arg_op (name, al) -> let rl = find_terms_id ts al interp in Thash.find ts.termhash (FTFunct(name, rl)), Some (FTFunct(name, rl)) 
  | Arg_cons (name, al) -> let rl = find_terms_id ts al interp in Thash.find ts.termhash (FTConstr(name, rl)), Some (FTConstr(name, rl)) 
  | Arg_record fld_list -> 
      let fl,al = List.split fld_list in 
      let rl = find_terms_id ts al interp in 
      let fld_list = List.combine fl rl in 
      Thash.find ts.termhash (FTRecord fld_list), Some (FTRecord fld_list)
  in r, 
    match ft with 
      Some ft ->
       Some (try List.find (fun t -> ft_eq (!t).term ft) (!r).terms with Not_found -> unsupported ())
    | None -> None
and find_terms_id (ts: term_structure) (tl : 'a args list) (interp : var_subst) : representative list = 
  List.map (fun x -> fst (find_term_id ts x interp)) tl 


let find_term (ts: term_structure) (t: 'a args) : representative =
  fst (find_term_id ts t empty_vs)      
and find_terms (ts: term_structure) (tl : 'a args list) : representative list = 
  find_terms_id ts tl empty_vs  


(* Code for substitutions on representatives *)
type representative_subst = 
  | Plain of rmap 
  | Freshen of rmap * representative rhash_t * term_structure

let empty_subst () = Plain (rmap_empty () ) 
let apply_subst  (subst : representative_subst) r1 =
  let res = match subst with 
    Plain map -> 
      (try rmap_find r1 map with Not_found -> r1)
  | Freshen (map,hash,ts) -> 
      (try rmap_find r1 map
      with Not_found -> 
	try Rhash.find hash r1 
	with Not_found -> let r2 = next_rep () in ts.repset <- Rset.add r2 ts.repset; Rhash.add hash r1 r2; r2)
  in if ts_debug then Format.fprintf !dump  "Subst %a for %a.\n" string_rep_db r1  string_rep_db res; res

let apply_subst_ft (subst : representative_subst) ft = 
  match ft with 
    FTConstr (name,rl) ->  
      let rl = List.map (apply_subst subst) rl in 
      FTConstr(name, rl), rl
  | FTFunct (name,rl) -> 
      let rl = List.map (apply_subst subst) rl in 
      FTFunct(name, rl),rl
  | FTRecord fld_list -> 
      if ts_debug then Format.fprintf !dump  "Before subst %a\n" string_ft_db ft;
      let fl,rl = List.split fld_list in 
      let rl = List.map (apply_subst subst) rl in 
      let ft = FTRecord (List.combine fl rl) in 
      if ts_debug then Format.fprintf !dump  "After subst %a\n" string_ft_db ft;
      ft,rl 
  | FTString _ 
  | FTPVar _ -> ft, [] 
  

(* INTERNAL *)
let rep_subst r1 r2 =
  fun r -> if rep_eq r1 r then (if ts_debug then Format.fprintf !dump  "Replace %a with %a\n" string_rep_db r  string_rep_db r2; r2) else r 
    
let rep_pair_list_subst r1 r2 rl =
  map_option 
    (fun (ra,rb) -> 
      let ra = rep_subst r1 r2 ra in 
      let rb = rep_subst r1 r2 rb in 
      if rep_eq ra rb then None else Some (ra,rb)) rl

let extend_subst (subst : representative_subst) r1 r2 = 
  if ts_debug then Format.fprintf !dump  "Extend subst with %a |-> %a\n" string_rep_db r1 string_rep_db r2;
  match subst with 
    Plain map -> if rmap_mem r1 map then unsupported () else Plain 
      (rmap_add r1 r2 (rmap_map (rep_subst r1 r2) map))
  | Freshen (map,hash,ts) -> unsupported ()


(*let freshening_subs ts (subst :representative_subst) = 
  match subst with
    Plain map -> Freshen (map,Rhash.create(20),ts)
  | _ -> unsupported () 
*)



(* INTERNAL *)
(* Updates the term t to use r2 instead of r1 in its representation *)
(* Returns None, if the updated term doesn't already exist.
   Otherwise, returns Some of a pair of representations that should be made equal. *)
let term_update ts term_id r1 r2 =
  let t = (!term_id).term in 
  (* find representation for current term *)
  let rc = (!term_id).rep in 
  if not (!r1).deleted then unsupported ();
  if (!r2).deleted then unsupported ();
  if not (Rset.mem r1 (rv_ft t Rset.empty)) then Inl term_id
  else(
  if ts_debug then Format.fprintf !dump  "Update %a to %a in %a\n" string_rep_db r1   string_rep_db r2   string_ft_db t;
  let new_t =  
    match t with 
      FTConstr (name,rl) ->  FTConstr(name, List.map (rep_subst r1 r2) rl)  
    | FTFunct (name,rl) -> FTFunct(name, List.map (rep_subst r1 r2) rl)
    | FTRecord fld_list -> 
	let fl,rl = List.split fld_list in 
	let rl = List.map (rep_subst r1 r2) rl in 
	FTRecord (List.combine fl rl)
    | FTString string -> unsupported ()
    | FTPVar var -> unsupported ()    
  in
  (try if ts_debug then print_termhash ts; Thash.remove ts.termhash t with Not_found -> unsupported ()) ;
  if ts_debug then (Format.fprintf !dump  "Updated %a to %a in %a of %a\n" string_rep_db r1  string_rep_db r2   string_ft_db new_t   string_rep_db rc; print_termhash ts);
  (* remove current term from map *)
  try 
    (let r_new = Thash.find ts.termhash new_t in 
    if ts_debug then 
      Format.fprintf !dump  "Found %a in %a so remove old term %a from %a" string_ft_db new_t   string_rep_db r_new   string_ft_db t   string_rep_db rc;
    (* Do not need to insert new term, it already exists, 
       the returned pair will collapse the relevant things recursively *)
    try
      (* Remove old uses of this term *)
      let subterms = rv_ft t Rset.empty in 
      Rset.iter
	(
	 fun sub_term ->
	   (!sub_term).uses <- List.filter (fun tid -> not(tid == term_id)) (!sub_term).uses
	)
	subterms;
      (* Remove term from my representative *)
      if ts_debug then Format.fprintf !dump  "Pre update %a.\n" string_ts_db ts;
      let tl = (!rc).terms in 
      (!rc).terms <- List.filter (fun tid-> not (tid == term_id)) tl;
      if ts_debug then Format.fprintf !dump  "Mid update after filtering %a to remove %a from\n %a.\n" string_rep_db rc   string_ft_db t   string_ts_db ts;
 (*     TIDhash.remove ts.termids2terms term_id;*)
      if ts_debug then Format.fprintf !dump  "Need to make %a equal to %a.\n" string_rep_db rc   string_rep_db r_new;
      Inr (r_new,rc)
    with Not_found -> unsupported ())
  with Not_found -> 
    (try 
      (* Insert new one *)
      assert(not(Thash.mem ts.termhash new_t));
      Thash.add ts.termhash new_t rc; 
      (* update the term_id to term map with new term *)
      (!term_id).term <- new_t;
      Inl term_id
    with Not_found -> unsupported ())
)


let well_formed_rep rep = 
  if (!rep).deleted then unsupported ();
  let rs = List.map (fun x-> (!x)) (!rep).uses in 
  if List.exists (fun x-> (!(x.rep)).deleted) rs then
    (List.iter (fun r -> Format.fprintf !dump  "%a used in %a of %a" string_rep_db rep   string_ft_db r.term   string_rep_db (r.rep)) rs; unsupported ());
  if List.for_all (fun x-> Rset.mem rep (rv_ft (x.term) Rset.empty)) rs then () else unsupported () 
  

	  
(* Makes each pair in eqs equal *)
let rec make_equal (ts : term_structure) (eqs : (representative * representative) list) (subst : representative_subst) =
  match eqs with 
    [] -> 
      if ts_debug then (Format.fprintf !dump  "Finished equalising \n %a \n\n" string_ts_db ts; print_termhash ts);
      subst
  | (r1,r2)::eqs ->
      let r1 = apply_subst subst r1 in 
      let r2 = apply_subst subst r2 in 
      if ts_debug then 
	(
	Format.fprintf !dump  "Make %a and %a equal  (current eqs=%a) in\n%a\n\n" 
	  string_rep_term_db r1 
	  string_rep_term_db r2 
	  (Debug.list_format "," (fun ppf (x,y) -> Format.fprintf ppf "%a=%a" string_rep_db x   string_rep_db y)) eqs 
	  string_ts_db ts; 
	print_termhash ts);
      well_formed_rep r1;
      well_formed_rep r2;
      if rep_eq r1 r2 then make_equal ts eqs subst else 
      ((*assert
	(
	 let rs = accessible_rs ts in 
	 if Rset.mem r1 rs && Rset.mem r2 rs then true
	 else (
	   Printf.printf "Can't make equal, not it term_structure." ; false
	  )
	);*)
      (* Collapse the two representative sets *)
      let tl1 = (!r1).terms in
      let tl2 = (!r2).terms in
      (*  Find records contained in either *)
      let rec1 = List.filter (fun t -> match (!t).term with FTRecord(_) -> true | _ -> false) tl1 in 
      let rec2 = List.filter (fun t -> match (!t).term with FTRecord(_) -> true | _ -> false) tl2 in 
      let eqs = match rec1,rec2 with
	[t1],[t2] -> 
	  let FTRecord fld1, FTRecord fld2 = (!t1).term,(!t2).term in 
	  let fl1,rl1=List.split fld1 in
	  let fl2,rl2=List.split fld2 in 
	  if fl1=fl2 then 
	    (List.combine rl1 rl2)  @ eqs
	  else (* TODO: contradiction *) eqs
      | _ -> eqs  (* TODO: Do other cases properly *) in
      (* Update pending eqs with this one *)
 (*     let eqs = rep_pair_list_subst r2 r1 eqs in*)
      (* Add all uses of the old representative in the uses map to point to remaining representative *) 
      (* Merge the two lists *)
      let tl1 = (* List.merge *) tl1 @ tl2 in 
      (* TODO: Remove redundancy *)
      (* TODO: Constructor stuff? *)
      (!r1).terms <- tl1; 
      if ts_debug then 
	Format.fprintf !dump  "Moving terms %a from %a to %a.\n" 
	  (Debug.list_format "," (fun ppf t2 -> string_ft_db ppf(!t2).term)) tl2
	  string_rep_db r2 
	  string_rep_db r1;
      List.iter 
	(fun t2 ->
	if ts_debug then Format.fprintf !dump  "Moving %a from %a to %a\n" string_ft_db (!t2).term   string_rep_db r2   string_rep_db r1;
	try 
	  assert
	    (
	     let r = rep_eq (apply_subst subst (Thash.find ts.termhash ((!t2).term))) r2 in 
	     if not r then (
	       Format.fprintf !dump  "Current maps subst(%a)=%a, expected %a\n"
		 string_rep_db (Thash.find ts.termhash ((!t2).term))
		 string_rep_db (apply_subst subst (Thash.find ts.termhash ((!t2).term)))
		 string_rep_db r2;
	       Thash.iter (
	       fun term rep ->
		 Format.fprintf !dump  "  %a,%a\n"  string_ft_db term   string_rep_db rep;
	      ) ts.termhash
	      );
	      r
	    ); 
	  Thash.remove ts.termhash ((!t2).term);
	  if ts_debug then Format.fprintf !dump  "Removed from hash!\n";
	  assert(not(Thash.mem ts.termhash (!t2).term));
	  Thash.add ts.termhash ((!t2).term) r1; 
	  (!t2).rep <- r1
	with Not_found -> 
	  Format.fprintf !dump  "Failed to find %a\nIt contains \n"  string_ft_db ((!t2).term); 
	  print_termhash ts;
	  unsupported () 		
	) tl2;
      (* Find the uses of the old representations *)
      let uses = (!r2).uses in
      (!r2).uses <- [];
      (!r2).terms <- [];
      (!r2).deleted <- true;
      if ts_debug then Format.fprintf !dump  "Rep %a used in %a\n" string_rep_db r2  string_tlist uses;
      (* Find all occurances of old representative and change to remaining representative
	 producing equalities and the uses that remain *)
      let uses,new_eqs = map_sum (fun t -> try term_update ts t r2 r1 with Not_found -> unsupported ()) uses  in 
      let eqs = eqs @ new_eqs in
      (* Update the uses to the only contain current terms, and merge other term *)
      let uses2 = (!r1).uses in
      (!r1).uses <- uses2 @ uses; 
      well_formed_rep r1;
      make_equal ts eqs (extend_subst subst r2 r1))


let rec add_equal_i (ts : term_structure) (r1 : representative) (r2 : representative) subst=
  try 
    make_equal ts [r1,r2]  subst 
  with Not_found -> Format.fprintf !dump  "Failed ts: %a\n" string_ts_db ts; unsupported ()

let rec add_equal (ts : term_structure) (r1 : representative) (r2 : representative) =
  add_equal_i ts r1 r2 (empty_subst())

let rec try_equal_i (ts : term_structure) (r1 : representative) (r2 : representative) 
    (rs_context : rset_t) subst = 
  (* *)
  if ts_debug then
    Format.fprintf !dump  "Trying to unify %a with %a\n" string_rep_db r1  string_rep_db r2;
  (* perform occurs check. *)
  let rs_context = rv_trans_set rs_context in 
  if (is_existential ts r1 && not (Rset.mem r1 rs_context) )
  || (is_existential ts r2 && not (Rset.mem r2 rs_context) )
  then 
  (let rs = rv_transitive r1 in 
  let rs2 = rv_transitive r2 in 
  if Rset.mem r2 rs || Rset.mem r1 rs2 then subst else (add_equal_i ts r1 r2 subst))
  else 
  (* Record unification *)
  try 
    let rec1 = List.find (fun x -> match (!x).term with FTRecord _ -> true | _ -> false) (!r1).terms in 
    let rec1 = match (!rec1).term with FTRecord l -> l | _ -> unsupported ()  in 
    let rec2 = List.find (fun x -> match (!x).term with FTRecord _ -> true | _ -> false) (!r2).terms in 
    let rec2 = match (!rec2).term with FTRecord l -> l | _ -> unsupported ()  in 
    (List.fold_right2 
      (fun (f1,r1) (f2,r2) subst -> 
	try_equal_i ts (apply_subst  subst r1) (apply_subst subst r2) rs_context subst
      ) rec1 rec2 subst)
  with Not_found -> subst



let setmap  f set =
  Rset.fold  (fun x set ->  Rset.add (f x) set) set Rset.empty

    
let try_equal a b c d = try_equal_i a b c d (empty_subst ())

(* Creates an empty term structure *)
let blank () =
  {
   termhash = Thash.create 20;
   repset = Rset.empty
 }


(*IF-OCAML*)
module Tmap = Map.Make(struct
   type t = term
   let compare = t_compare
end)
(*ENDIF-OCAML*)    
(*F#
let Tmap = Map.Make(t_compare)
F#*)

(* Copies an existing term structure,  they are not functional so necessary *)
let clone (ts : term_structure) (rs : rset_t) abs : term_structure * representative_subst =
  if ts_debug then Format.fprintf !dump  "Starting clone\n %a  \nThash: %a\n" string_ts_db ts printf_thash ts;
  let newts = blank() in
  let rs = Rset.union (rv_trans_set rs) (accessible_rs ts) in 
  (*  Add new exists reps to the context one for each current representative, and build substitution *)
  let subst = 
    Rset.fold
      (fun key subst -> 
	(* COMMENTS SO demo works in Baltimore.....
	   if (!key).deleted then 
	  (Printf.printf "Trying to copy deleted representative: %s" (string_rep_db key)(*; unsupported ()*) );*)
	let new_rep = add_existential newts in
	extend_subst subst key new_rep)
      rs
      (empty_subst ()) in 
  (* For each representative, create its terms, and build a subst on them *)
  let tsubst = Rset.fold 
    (fun rep tsubst->
      (* For each term, add it to termstructure *)
      if ts_debug then Format.fprintf !dump  "Cloning terms for representative %a\n" string_rep_db rep;
      let terms = (!rep).terms in 
      let newrep = apply_subst  subst rep in 
      let newterms,tsubst = List.fold_right
	  (fun term_id (terms,tsubst) -> 
	    if abs && !term_id.redundant then (terms,tsubst)
	    else (
	      let newterm,_ = apply_subst_ft subst (!term_id).term in
	      if ts_debug then Format.fprintf !dump  "Cloning %a with %a\n." string_ft_db (!term_id).term   string_ft_db newterm;
	      let newtref = new_term newrep newterm (!term_id).redundant in
	      let tsubst = Tmap.add term_id newtref tsubst in 
	      assert(not(Thash.mem newts.termhash newterm));
	      Thash.add  newts.termhash newterm newrep;
	      (newtref::terms,tsubst)
		)
	  ) terms ([],tsubst) in
      (!newrep).terms <- newterms; tsubst
    ) rs Tmap.empty in 
(* Update uses to be new terms *)
  Rset.iter 
    (fun rep -> 
      let newrep = apply_subst  subst rep in 
      (!newrep).uses <- map_option 
	  (fun t -> 
	    try 
	      Some (Tmap.find t tsubst)
	    with Not_found -> 
	      if ts_debug then Format.fprintf !dump  "Not used %a\n" string_ft_db (!t).term;
	      None) 
	  (!rep).uses
    ) rs;
  newts.repset <- setmap (apply_subst subst) ts.repset;
  if ts_debug then Format.fprintf !dump  "Finished clone\n";
  if ts_debug then Format.fprintf !dump  "%a" printf_thash newts;
  newts,subst

    
(*let remove_term ts ft =
  let r = Thash.find ts ft in 
  let tl = (!r).terms in
  let tidr = List.find (fun tid -> ft_eq (!tid).term ft) tl in 
  (!r).terms <- List.filter (fun tid -> tid == tidr) tl;
  let subterms = rv_ft ft Rset.empty in 
  Rset.iter
    (
     fun sub_term ->
       (!sub_term).uses <- List.filter (fun tid -> not (tid == tidr)) (!sub_term).uses
    )
    subterms
*)

(* let add_term_to_rep ts ft r = *)


(* Remove the program variable from the term structure *)
let rec kill_var (ts : term_structure) (v : Vars.var) = 
  try 
    if ts_debug then Format.fprintf !dump  "Kill %s\n" (Vars.string_var v);
    let r = find_term ts (Arg_var v) in 
    if ts_debug then Format.fprintf !dump  "Rep currently looks like: %a\n" string_rep_term_db r;
    let tl = (!r).terms in
    let tl = List.filter (fun tid -> match ((!tid).term) with FTPVar v' -> v != v' | _ -> true) tl in 
    (!r).terms <- tl;
    if ts_debug then Format.fprintf !dump  "After update looks like: %a\n" string_rep_term_db r;
    Thash.remove ts.termhash (FTPVar v)
  with Not_found -> 
    if ts_debug then Format.fprintf !dump  "Failed to find : %s\n" (Vars.string_var v)

(* Takes a term structure, and a context in which it will be tried to satisfied 
   and returns a list of equalities between representatives, and a substitution 
   to move terms using the terms structure to now use the context. *)
let rec ts_to_eqs (ts : term_structure) (context : term_structure) (rs : rset_t) : (representative * representative) list  * representative_subst = 
  let rs = Rset.union (rv_trans_set rs) (accessible_rs ts) in 
  (*  Add new exists reps to the context one for each current representative, and build substitution *)
  let subst = 
    Rset.fold
      (fun key subst -> 
	let new_rep = add_existential context in
	extend_subst subst key new_rep)
      rs
      (empty_subst ()) in 
  (* Add all terms to the context, and produce equality for each one *)
  let equals = Rset.fold 
      (fun rep equals-> 
	let new_rep = apply_subst subst rep in
	List.fold_left
	   (fun equals termid ->
	     let term = (!termid).term in
	     let new_term,rl = apply_subst_ft subst term in 
	     let rep,tid = add_flat_term context new_term rl (!termid).redundant in 
	     (rep,new_rep)::equals
	   )  equals (!rep).terms 
      ) rs [] in
  (* return list of equalities and substitution *)
  (equals,subst)



(* Checks if representative matchs pattern,
 calls continuation if it matches
 if continuation throws No_match tries a different match 
 otherwise throws No_match. *)
let rec unifies (ts : term_structure) (p : representative args) (r : representative)  (forbidden_tids : TIDset.t) (interp : var_subst) (cont : var_subst -> 'a) : 'a  = 
    match p with 
    | Arg_var (Vars.EVar _) -> 
	if is_existential ts r then () else raise No_match; (* must be an existential variables *)
	(match p with Arg_var v -> 
	(try 
	  let rep = find_vs ts v interp in 
	  if rep_eq rep r then cont interp else raise No_match
	with Not_found -> cont (add_vs v r interp)
	) | _ -> unsupported ())
    | Arg_var (Vars.PVar _) 
    | Arg_string _ 
      -> 
	(try 
	  let rep_id = find_term ts p in
	  if rep_eq rep_id r then cont interp
	  else raise No_match
	with Not_found -> raise No_match)
    | Arg_var (Vars.AnyVar (i,j)) -> 
	(try 
	  let rep = find_vs ts (Vars.AnyVar (i,j)) interp in 
	  if rep_eq rep r then cont interp else raise No_match
	with Not_found -> cont (add_vs (Vars.AnyVar (i,j)) r interp)
	)
    | Arg_op (name, al) -> 
	let termids = (!r).terms in 
	let terms = map_option 
	    (fun tid -> 
	      if TIDset.mem tid forbidden_tids then None else 
	      let t = (!tid).term in
	      match t with FTFunct(n,rl) when n=name -> Some rl | _ -> None) termids in 
	let rec f rls =
	  match rls with 
	    [] -> raise No_match
	  | rl::rls -> 
	      try unifies_list ts al rl forbidden_tids interp cont 
	      with No_match -> f rls  
	in f terms
    | Arg_cons (name, al) ->
 	let termids = (!r).terms in 
	let terms = map_option 
	    (fun tid -> 
	      let t = (!tid).term in
	      match t with FTConstr(n,rl) when n=name -> Some rl | _ -> None) termids in 
	let rec f rls =
	  match rls with 
	    [] -> raise No_match
	  | rl::rls -> 
	      try unifies_list ts al rl forbidden_tids interp cont 
	      with No_match -> f rls  
	in f terms
    | Arg_record fldlist ->
	let flds,al = List.split fldlist in
	let termids = (!r).terms in 
	let terms = List.map (fun tid -> (!tid).term) termids in 
	let terms = map_option 
	    (fun t -> match t with 
	      FTRecord(rfl) -> let flds2,rl = List.split rfl in if flds2=flds then Some rl else None 
	    | _ -> None) 
	    terms in 
	let rec f rls =
	  match rls with 
	    [] -> raise No_match
	  | rl::rls -> 
	      try unifies_list ts al rl forbidden_tids interp cont 
	      with No_match -> f rls  
	in f terms
and unifies_list ts al rl (forbidden_tids : TIDset.t) interp cont =
  match al,rl with
    [],[] -> cont interp 
  | _,[] -> raise No_match
  | [],_ -> raise No_match 
  | a::al,r::rl -> unifies ts a r forbidden_tids interp (fun interp -> unifies_list ts al rl forbidden_tids interp cont)

let unifies_list_ntids = unifies_list

let unifies ts a r i c = unifies ts a r TIDset.empty i c

let unifies_list ts al rl i c = unifies_list ts al rl TIDset.empty i c 

let rec unifies_eq_inner ts rl a1 a2 interp cont =
  match rl with 
    [] -> raise No_match
  | r::rl -> if ts_debug then Format.fprintf !dump  "Trying representative@ %a@ for@ %a =@ %a.@\n" string_rep_term_db r string_args a1 string_args a2;
    (try 
      if ts_debug then Format.fprintf !dump  "Trying to match %a in %a.@\n" string_args a1  string_rep_term_db r;
      unifies ts a1 r interp
        ( fun interp-> 
	  if ts_debug then Format.fprintf !dump  "Trying to match %a in %a.@\n" string_args a2  string_rep_term_db r;
          unifies ts a2 r interp 
            ( fun interp ->
              try 
(* TODO: This code doesn't seem necessary any more, but lets see *)
(*                let tid = match find_term_id ts a2 interp with _,Some tid -> tid | _ -> raise No_match in
                let tid2= match find_term_id ts a1 interp with _,Some tid -> tid | _ -> raise No_match in
                let b = tid==tid2 in 
		if b then Printf.printf "Foooooo %s\n" (string_rep_term_db r);
                if b then raise No_match else (cont interp) *)
		  cont interp 
              with Not_found -> unsupported ()
            )
        )
    with No_match -> unifies_eq_inner ts rl a1 a2 interp cont)

let unifies_eq ts rs a1 a2 interp cont =
  let rl = Rset.elements (Rset.union (rv_trans_set rs) (accessible_rs ts)) in 
  unifies_eq_inner ts rl a1 a2 interp cont






type 'a rewrite_entry =  ((representative args) list * (representative args) * 'a * string * bool) list

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


exception Done

let rewrite_ts (ts : term_structure) (rm : 'a rewrite_map) dtref rs (query : var_subst * 'a -> var_subst option) = 
  let x = ref true in
  let subst = ref (empty_subst () )in
  if ts_debug then Format.fprintf !dump  "Trying to rewrite stuff!\n";
  if ts_debug then Format.fprintf !dump  "Trying to rewrite stuff!\n";
  try 
    Thash.iter 
    (
     fun ft repid ->
       if (!repid).deleted then unsupported () else (
       if ts_debug then Format.fprintf !dump  "Trying to rewrite: %a of %a@\n" string_ft_db ft   string_rep_db repid;
       match ft with 
	 FTFunct(name, rl) ->
	   (try 
	     let rws = rm_find name rm in
	     List.iter 
	       (
		fun (al,a,extra,rule,redundant) ->
		  try
		    if ts_debug then Format.fprintf !dump  "Trying rule:%s@\n" rule;
		    unifies_list_ntids ts al rl !dtref empty_vs
		      (fun interp 
			-> 
			  (* Hack for exists so they are not in context by default *)
			  if (List.exists2 
				(fun r a -> 
				  match a with 
				    Arg_var (Vars.EVar _) 
				    -> 
				      let b = Rset.mem r rs in
				      if ts_debug && b then Format.fprintf !dump  "Not a free exists.@\n"; b 
				  | _ -> false) 
				rl al) 
			  then raise No_match; 
			  (* end Hack *)
			  let interp = match query (interp,extra) with None ->  raise No_match | Some interp -> interp in 
			  let tid : term =  (List.find (fun (y : term)-> ft_eq (!y).term ft) (!repid).terms) in
			  if TIDset.mem tid !dtref then raise No_match;
			  let r,i,t = add_term_id ts interp a (redundant || !tid.redundant) in 
			  if (true || !(Debug.debug_ref)) && not(rep_eq r repid) then 
			    Format.fprintf !dump "Using rule:@ %s@ gives@ %a@ equal to %a.@\n" rule 
			      (string_rep_term (rao_create ())) r  
			      (string_rep_term (rao_create ())) repid;
			  if rep_eq r repid then 
			    (match t with 
			      Some (Inr ti) -> (* Term has been added *)
				if TIDset.mem ti !dtref && not redundant then () else 
				( dtref:=TIDset.add tid !dtref;
				 if ts_debug then Format.fprintf !dump  "Add removal flag to:%a@\n"  string_term tid)
			    | Some (Inl ft) -> (* Lookup term id, as it preexisted *)
				let ti : term =  (List.find (fun (y : term)-> ft_eq (!y).term ft) (!r).terms) in 
				if TIDset.mem ti !dtref then () else 
				( dtref:=TIDset.add tid !dtref ;
				 if ts_debug then Format.fprintf !dump  "Add removal flag to:%a@\n"  string_term tid)
			    | _ -> 
				(* This means we have a anyvar on the right, I think, so should remove term *)
				dtref:=TIDset.add tid !dtref ;
				if ts_debug then Format.fprintf !dump  "Add removal flag to:%a@\n"  string_term tid
			    )
			  else
			  (if ts_debug then Format.fprintf !dump  "Make eq: %a %a\n" string_rep_term_db r    string_rep_term_db repid;
			   (* if r does not use tid, then it should be removed later TODO make transitive check*)
			   if Rset.exists (fun r ->  (List.exists ((==) tid) (!r).terms)) (rv_transitive r) then () else (
			   if ts_debug then Format.fprintf !dump  "Add removal flag to:%a@\n"  string_term tid;  
			       dtref := TIDset.add tid !dtref);			         
			   (* Make terms equal *)
			   subst := make_equal ts [r,repid] !subst;
			   x := true;
			   if ts_debug then Format.fprintf !dump  "Rewritten ts: %a@\n" string_ts_db ts;
			   if ts_debug then Format.fprintf !dump  "Done rule:%s@\n" rule; raise Done); 
			  well_formed_rep repid; 
			  well_formed_rep r;
		      )
		  with No_match -> ()
	       ) rws 
	   with Not_found -> ()
	   )
       | _ -> ()
      )
    ) ts.termhash;
    raise No_match
  with Done ->
    (if ts_debug then (Format.fprintf !dump  "Finished rewrites!@\n"; print_termhash ts);
    !subst)


let kill_all_exists_names ts =
  let rs = accessible_rs ts in
  Rset.iter 
    (fun rid -> 
      (!rid).terms <- List.filter  (fun x -> match (!x).term with FTPVar (Vars.EVar _) -> (Thash.remove ts.termhash (!x).term ); false |_-> true)  (!rid).terms
    )
    rs



let kill_term_set ts tidset = 
   TIDset.iter 
   (
    fun tid -> 
      if ts_debug then Format.fprintf !dump  "Removing term:%a@\n"  string_term tid;
      let rid = (!tid).rep in 
      let terms = List.filter (fun t -> not (t == tid)) (!rid).terms in   
      (!rid).terms <- terms;
      Thash.remove ts.termhash (!tid).term ;
      let subterms = rv_ft (!tid).term Rset.empty in 
      Rset.iter
	(
	 fun sub_term ->
	   (!sub_term).uses <- List.filter (fun tid2 -> not (tid2 == tid)) (!sub_term).uses
	)
	subterms
   )
   tidset

