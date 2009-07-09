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
type 'a args = 
  | Arg_var of Vars.var
  | Arg_string of string
  | Arg_op of string * 'a args list
  | Arg_cons of string * 'a args list  (* Do not use *)
  | Arg_record of (string * 'a args) list (* Do not use *)
  | Arg_hole of 'a

let mkArgRecord fldlist =
  Arg_record (List.sort (fun (a1,b1) (a2,b2) -> compare a1 a2) fldlist)

type 'a fldlist = (string * 'a args) list

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

type 'a varmapargs = ('a args) varmap_t

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
type 'a varhashargs = ('a args) VarHash.t  
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



type 'a varmap = 
  | Plain of ('a varmapargs)
  | Freshen of ('a varmapargs) *  'a varhashargs


let find key (map : 'a varmap) = 
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
 
let add (key : Vars.var)  (v : 'a args)  (map : 'a varmap) : 'a varmap =
  match map with 
    Plain map -> Plain (vm_add key v map)
  | Freshen (map,h) -> Freshen((vm_add key v map),h)

let empty : 'a varmap = Plain (vm_empty)


let freshening_subs subs : 'a varmap =
    match subs with 
      Plain subs -> Freshen (subs, vh_create 30 )
    | _ -> unsupported ()



let subst_kill_vars_to_fresh_prog vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshp())) vm) vars vm_empty)

let subst_kill_vars_to_fresh_exist vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshe())) vm) vars vm_empty)

let subst_freshen_vars vars = 
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshen ev)) vm) vars vm_empty)


(* substitution code for formula *)
let subst_var subs v = (try find v subs with Not_found -> Arg_var v)

let rec subst_args subs arg : 'a args= 
  match arg with 
  | Arg_var v -> (subst_var subs v)
  | Arg_string s -> Arg_string s
  | Arg_op (name,args) -> Arg_op(name,List.map (subst_args subs) args)
  | Arg_cons (name,args) -> Arg_cons(name,List.map (subst_args subs) args)
  | Arg_record fldlist -> Arg_record (List.map (fun (f,v) -> f,subst_args subs v) fldlist)	
  | Arg_hole a -> unsupported ()

let rec string_args ppf arg = 
  match arg with 
  | Arg_var v -> Format.fprintf ppf "%s" (string_var v)
  | Arg_string s -> Format.fprintf ppf "\"%s\""  s 
  | Arg_op (name,args) -> Format.fprintf ppf "%s(%a)" name string_args_list args 
  | Arg_cons (name,args) -> Format.fprintf ppf "%s(%a)" name string_args_list args 
  | Arg_record fldlist -> 
      Format.fprintf ppf "@[{%a}@]" string_args_fldlist fldlist
  | Arg_hole a -> unsupported ()
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



let rec string_args_hole f ppf arg = 
  match arg with 
  | Arg_var v -> Format.fprintf ppf "%s" (string_var v)
(*  | Arg_string s -> "\"" ^ s ^ "\""*)
  | Arg_string s -> Format.fprintf ppf "%s" s 
  | Arg_op (name,args) -> Format.fprintf ppf "@[%s(%a)@]" name (string_args_list_hole f) args 
  | Arg_cons (name,args) -> Format.fprintf ppf "@[%s(%a)@]" name (string_args_list_hole f) args 
  | Arg_record fldlist -> 
      Format.fprintf ppf "@[{%a}@]" (string_args_fldlist_hole f) fldlist
  | Arg_hole a -> Format.fprintf ppf "%a" f a
and string_args_list_hole f ppf argsl = 
  Debug.list_format "," (string_args_hole f) ppf argsl
and string_args_fldlist_hole f ppf argsl = 
  Debug.list_format "," (fun ppf (fd,a) -> Format.fprintf ppf "%s=%a" fd (string_args_hole f) a) ppf argsl




let rec hole_replace (f : 'a -> 'b args) (arg : 'a args) : 'b args = 
  match arg with 
  | Arg_var _ 
  | Arg_string _ -> arg
  | Arg_op (name,args) -> Arg_op(name, hole_replace_list f args)
  | Arg_cons (name,args) -> Arg_cons(name, hole_replace_list f args)
  | Arg_record fldlist -> 
      Arg_record (List.map (fun (a,b) -> a,(hole_replace f b)) fldlist) 
  | Arg_hole a -> f a
and hole_replace_list f argsl = 
  (List.map (hole_replace f) argsl)


