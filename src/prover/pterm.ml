(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)


(************************************************************
   The syntactic representation of terms.
*************************************************************)
open Debug
open Vars
(*F#
open Microsoft.FSharp.Compatibility
F#*)

(* Main terms *)
type args = 
  | Arg_var of Vars.var
  | Arg_string of string
  | Arg_op of string * args list
  | Arg_cons of string * args list  (* Do not use *)
  | Arg_record of (string *  args) list (* Do not use *)

let mkArgRecord fldlist =
  Arg_record (List.sort (fun (a1,b1) (a2,b2) -> compare a1 a2) fldlist)

type fldlist = (string * args) list

(* Type for substitution on variables in programs *)
(*IF-OCAML*) 
module VarSet =
  Set.Make(struct
    type t = var
    let compare = compare
  end)
type varset = VarSet.t
(*ENDIF-OCAML*)

(*F#
module VarSet = Set
type varset = var VarSet.t
F#*)


let vs_mem = VarSet.mem
let vs_add = VarSet.add
let vs_empty = VarSet.empty
let vs_fold = VarSet.fold
let vs_iter = VarSet.iter
let vs_diff = VarSet.diff
let vs_exists = VarSet.exists
let vs_from_list vl = List.fold_right (fun vs v -> vs_add vs v) vl vs_empty


(*IF-OCAML*)
module VarMap = 
  Map.Make(struct
    type t = Vars.var
    let compare = compare
  end)   

type 'a varmap_t = 'a VarMap.t
(*ENDIF-OCAML*)

(*F#
module VarMap = Map
type 'a varmap_t = VarMap.t<Vars.var,'a> 
F#*)

type varmapargs = args varmap_t

let vm_add = VarMap.add
let vm_empty = VarMap.empty
let vm_find = VarMap.find
let vm_mem = VarMap.mem
let vm_is_empty = VarMap.is_empty

(*IF-OCAML*)
module VarHash = Hashtbl.Make(struct 
    type t = Vars.var
    let equal = (=)
    let hash = Hashtbl.hash
  end)
type varhashargs = args VarHash.t  
type 'a varhash_t = 'a VarHash.t
(*ENDIF-OCAML*)
 
(*F# 
module VarHash = Hashtbl
type 'a varhash_t = VarHash.t<Vars.var,'a>
type 'a varhashargs = ('a args) varhash_t
F#*)

let vh_create = VarHash.create 
let vh_add = VarHash.add
let vh_find = VarHash.find



type varmap = 
  | Plain of varmapargs
  | Freshen of varmapargs *  varhashargs


let find key (map : varmap) = 
  match map with 
    Plain map -> vm_find key map  
  | Freshen (map,h) ->( 
      try vm_find key map 
      with Not_found -> 
	try vh_find h key
	with Not_found -> 
	  let newvar = Arg_var (freshen key) in 
	  vh_add h key newvar;
	  newvar
     )
 
let add (key : Vars.var)  (v : args)  (map : varmap) : varmap =
  match map with 
    Plain map -> Plain (vm_add key v map)
  | Freshen (map,h) -> Freshen((vm_add key v map),h)

let empty : varmap = Plain (vm_empty)


let freshening_subs subs : varmap =
    match subs with 
      Plain subs -> Freshen (subs, vh_create 30 )
    | _ -> unsupported_s "freshening_subs applied to wrong argument type."



let subst_kill_vars_to_fresh_prog vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshp())) vm) vars vm_empty)

let subst_kill_vars_to_fresh_exist vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshe())) vm) vars vm_empty)

let subst_freshen_vars vars = 
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshen ev)) vm) vars vm_empty)


(* substitution code for formula *)
let subst_var subs v = (try find v subs with Not_found -> Arg_var v)

let rec subst_args subs arg : args= 
  match arg with 
  | Arg_var v -> (subst_var subs v)
  | Arg_string s -> Arg_string s
  | Arg_op (name,args) -> Arg_op(name,List.map (subst_args subs) args)
  | Arg_cons (name,args) -> Arg_cons(name,List.map (subst_args subs) args)
  | Arg_record fldlist -> Arg_record (List.map (fun (f,v) -> f,subst_args subs v) fldlist)	

let rec string_args ppf arg = 
  match arg with 
  | Arg_var v -> Format.fprintf ppf "%s" (string_var v)
  | Arg_string s -> Format.fprintf ppf "\"%s\""  s 
  | Arg_op ("builtin_plus",[a1;a2]) -> Format.fprintf ppf "(%a+%a)" string_args a1 string_args a2
  | Arg_op (name,args) -> Format.fprintf ppf "%s(%a)" name string_args_list args 
  | Arg_cons (name,args) -> Format.fprintf ppf "%s(%a)" name string_args_list args 
  | Arg_record fldlist -> 
      Format.fprintf ppf "@[{%a}@]" string_args_fldlist fldlist
and string_args_list ppf argsl = 
  match argsl with 
    [] -> Format.fprintf ppf ""
  | [a] -> Format.fprintf ppf "%a" string_args a
  | a::al -> Format.fprintf ppf "%a,@ %a" string_args a string_args_list al
and string_args_fldlist ppf fdl =  
  match fdl with 
    [] -> Format.fprintf ppf ""
  | [(f,a)] -> Format.fprintf ppf "%s=%a" f string_args a
  | (f,a)::fdl -> Format.fprintf ppf "%s=%a;@ %a" f string_args a string_args_fldlist fdl




let rec fv_args args set = 
  match args with
    Arg_var var -> vs_add var set 
  | Arg_string _ -> set
  | Arg_op (name,argsl) -> fv_args_list argsl set
  | Arg_cons (name,argsl) -> fv_args_list argsl set
  | Arg_record fldlist -> fv_fld_list fldlist set
and fv_args_list argsl set =
  match argsl with 
    [] -> set
  | args::argsl -> fv_args_list argsl (fv_args args set)
and fv_fld_list fldlist set =
  match fldlist with
    [] -> set
  | (f,args)::fldlist -> fv_fld_list fldlist (fv_args args set)
    


let rec ev_args args set = 
  match args with
    Arg_var var -> (match var with EVar _ -> vs_add var set | _ -> set )
  | Arg_string _ -> set
  | Arg_op (name,argsl) -> ev_args_list argsl set
  | Arg_cons (name,argsl) -> ev_args_list argsl set
  | Arg_record fldlist -> ev_fld_list fldlist set
and ev_args_list argsl set =
  match argsl with 
    [] -> set
  | args::argsl -> ev_args_list argsl (ev_args args set)
and ev_fld_list fldlist set =
  match fldlist with
    [] -> set
  | (f,args)::fldlist -> ev_fld_list fldlist (ev_args args set)
