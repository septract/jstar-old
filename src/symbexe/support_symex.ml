(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Jparsetree
open Vars
open Pterm
open Plogic
open Rlogic
open Config
open Support_syntax

let warning () =
  Printf.printf "%c[%d;%dm"  (Char.chr 0x1B ) 1 31

let good () =
  Printf.printf "%c[%d;%dm"  (Char.chr 0x1B ) 1 32 

let reset () =
  Printf.printf "%c[%dm" (Char.chr 0x1B) 0 


let file = ref ""

type var_hashtbl = (string, Vars.var) Hashtbl.t

(* table to connect local variables used in symbolic execution 
   to the internal representation Vars.var 
*)
let var_table : var_hashtbl = Hashtbl.create 1000


let var_table_add key v = 
  if symb_debug () then Printf.printf "\n\n Adding variable (%s, %s)\n" key (Vars.string_var v);
  Hashtbl.add var_table key v


let var_table_find key =
  try 
    Hashtbl.find var_table key
  with Not_found -> 
    let _ =Printf.printf "\n ERROR: cannot find variable for %s in the table. Abort! \n" key in
    assert false


(* given a variable it returns its key to use in the table *)
let variable2key v = Pprinter.variable2str v



(* ============== Conversion facilities ================ *)

(* 
int, long, float are all represented with the unary op "numeric_const".
 string constants with the unary op "string_const".
In this way we abstract from the differen numerical values as well as different strings.
*)
let constant2args c =
  match c with 
  | Null_const -> Arg_op("nil",[]) 
  | Int_const (s,n) -> 
      (
      match s with 
      |	Positive -> Arg_op("numeric_const",[Arg_string(Printf.sprintf "%d" n)])
      |	Negative -> Arg_op("negative",[Arg_op("numeric_const",[Arg_string(Printf.sprintf "%d" n)])]) 
	    )
  | Int_const_long _ -> Arg_op("numeric_const",[]) 
  | Float_const _ -> Arg_op("numeric_const",[]) 
  | String_const _ -> Arg_op("string_const",[]) 
  | Clzz_const _  -> assert false 

(* 
  default value for type 
  returns fresh exists var with n as its name base if 
   it doesn't know what to do.
*)
let default_for ty n = 
  try (
    match ty with 
      Void -> assert false
    | Non_void jty -> (
	match jty with  
	| Base (jbt,arraylist) -> (
	    match jbt,arraylist with 
	      Class_name _, _ 
	    | Null_type, _ 
	    | _, _::_ -> Arg_op("nil",[]) 
	    | Int,_  
	    | Char,_
	    | Short,_
	    | Byte,_
	    | Long,_ -> Arg_op("numeric_const",[Arg_string("0")])
	    | Float,_
	    | Double,_ -> Arg_var(Vars.freshe_str (Pprinter.name2str n))
	    | Boolean,_ -> Arg_op("false",[])
	   )
	| _ -> Arg_op("nil",[]) 
       )
   )
  with Assert_failure (e,i,j) -> Printf.printf "Default for failed on type %s.\n" (Pprinter.j_type2str ty); raise (Assert_failure(e,i,j) )


let signature2args si = 
  Arg_string(Pprinter.signature2str si)

  
let name2args n =
  match n with 
  | Quoted_name s 
  | Identifier_name s -> Arg_var(var_table_find (s))


let identifier2args s = 
    Arg_var(var_table_find (s))


let immediate2args im = 
  match im with 
  | Immediate_local_name n -> name2args n
  | Immediate_constant c -> constant2args c


let reference2args r = (* not sure we need this. Maybe we need reference2PPred*)
  match r with 
  |Array_ref (id,im) -> assert false 
  |Field_local_ref(n,si) -> assert false
  |Field_sig_ref(si) -> assert false

(*
let bop_to_prover_arg = function
	Jparsetree.And -> "builtin_and"
      | Jparsetree.Or -> "builtin_or"
      | Xor -> "builtin_xor"
      | Mod -> "builtin_mod"
      | Cmp 
      | Cmpg 
      | Cmpl -> assert false
      | Cmpeq -> "builtin_eq"
      | Cmpne -> "builtin_ne"
      | Cmpgt -> "builtin_gt"
      | Cmpge -> "builtin_ge"
      | Cmplt -> "builtin_lt"
      | Cmple -> "builtin_le"
      | Shl -> "builtin_shiftl"    
      | Shr -> "builtin_shiftr"
      | Ushr -> "builtin_ushiftr"
      | Plus -> "builtin_plus"
      | Minus -> "builtin_minus"
      | Mult -> "builtin_mult"
      | Div -> "builtin_div"
*)

(* for the moment only few cases are done of this. Need to be extended *)
let expression2args e = 
  match e with 
  | New_simple_exp ty -> assert false
  | New_array_exp (nv_ty,fad) -> assert false  
  | New_multiarray_exp (ty,adl) -> assert false  
  | Cast_exp (nv_ty,im) -> assert false  
  | Instanceof_exp (im,nv_ty) -> assert false  
  | Binop_exp (bop,im1,im2) -> 
      Arg_op(bop_to_prover_arg bop
	,   [immediate2args im1; immediate2args im2] )
  | Unop_exp (uop,im) -> assert false  
  | Invoke_exp ie -> assert false  
  | Immediate_exp im -> immediate2args im
  | Reference_exp r -> reference2args r (* do we need this translation of better to PPred???*)  


let variable2var v =
  var_table_find (variable2key v )  


let var2args x =Arg_var x 


let immediate2var e = 
  match immediate2args e with 
    Arg_var v -> v
  | _ -> assert false


(* ==============  printing facilities  ======================= *)
let form2str f = Plogic.string_form f

let print_formset s fs=  
  Format.printf "@\n%s@  [ @[%a@]@ ]@." 
    s  
    (fun ppf -> List.iter (fun f ->Format.fprintf ppf "@[%a@]@\n " (string_ts_form (Rterm.rao_create ())) f )) fs


(* =============   end printing facilities ==================== *)




let negate e =
  match e with
  | Binop_exp (Cmpeq,i1,i2) -> Binop_exp (Cmpne,i1,i2)  
  | Binop_exp (Cmpne,i1,i2) -> Binop_exp (Cmpeq,i1,i2)  
  | Binop_exp (Cmpgt,i1,i2) -> Binop_exp (Cmple,i1,i2)  
  | Binop_exp (Cmplt,i1,i2) -> Binop_exp (Cmpge,i1,i2)  
  | Binop_exp (Cmpge,i1,i2) -> Binop_exp (Cmplt,i1,i2)  
  | Binop_exp (Cmple,i1,i2) -> Binop_exp (Cmpgt,i1,i2)  
  | _ -> assert false (* ddino: many other cases should be filled in *)

(*
let bop_to_prover_pred bop i1 i2 = 
  [match bop with 
  | Cmpeq -> P_EQ (i1, i2)
  | Cmpne -> P_NEQ (i1, i2)   
  | Cmpgt -> P_PPred("GT",[i1; i2])
  | Cmplt -> P_PPred("LT",[i1; i2])
  | Cmpge -> P_PPred("GE",[i1; i2])
  | Cmple -> P_PPred("LE",[i1; i2])
  | _ -> Printf.printf "\n\n Operation %s not supported. Abort!" (Pprinter.binop2str bop);
      assert false (* ddino: many other cases should be filled in *)]
*)

let expression2pure e =
  match e with
  | Binop_exp (op,i1,i2) -> bop_to_prover_pred op (immediate2args i1) (immediate2args i2)
  | _ -> Printf.printf "\n\n Expression %s not supported. Abort!" (Pprinter.expression2str e);
      assert false (* ddino: many other cases should be filled in *)			      

(* ================= defines names for this, return and parameter =============== *)

let parameter n = "@parameter"^(string_of_int n)^":"

(* define the constant name for the return variable. *)
(*let name_ret_var mname = (Pprinter.name2str mname)^"$"^"ret_var"*)
let name_ret_var = "$"^"ret_var"


let this_var_name = Jlogic.this_var_name



(* ================= misc functions =============== *)


(* true if v is a primed variable *)
let is_primed (v: Vars.var) : bool = 
  match v with 
  | EVar _ -> true
  | _ -> false 






(* create the variable in the table for the object "this" *)
let mk_this_of_class () : Vars.var =
  let v=Vars.concretep_str this_var_name 
  in var_table_add (this_var_name) v;
  v

(* create entries in the variable table for a list of parameters *)
let mk_parameter_of_class (ps: Jparsetree.parameter list option) : unit =
  match ps with 
  | None -> ()
  | Some ps ->   
      for i=0 to List.length ps do
	let p=parameter i in 
	let v=Vars.concretep_str p
	in var_table_add p v
      done 



let get_class_name_from_signature si =
  match si with
  | Method_signature (c,_,_,_) -> c
  | Field_signature (c,_,_) ->c


let signature_get_name si =
  match si with 
  | Method_signature (_,_,n,_) -> n
  | Field_signature (_,_,n) -> n


let invoke_exp_get_signature ie =
  match ie with 
  | Invoke_nostatic_exp(_, _, si, _) -> si
  | Invoke_static_exp(si,_) -> si


(* true if e is a variable starting with $ sign. $variables are special variables 
in jimple and need to e treated in special way  *)
let is_dollar_variable e =
  match e with 
    Immediate_local_name (Identifier_name x) -> 
      (String.sub x 0 1) = "$" 
  | _ -> false



(* checks if x \in fset. membership is considered up to logical equivalence *)
let rec formset_mem lo x fset =
  match fset with 
  | [] -> false
  | y::fset' -> 
      ((Prover.check_implication lo x y) && (Prover.check_implication lo y x)) || (formset_mem lo x fset') 

let compact_formset lo xs = 
  let rec impl xs ys = 
    match ys with 
      [] -> xs
    | y::ys -> 
	let xs = List.filter 
	    (fun x -> 
	      if (Prover.check_implication lo x y) then false else true) xs in 
	let ys = List.filter 
	    (fun x -> 
	      if (Prover.check_implication lo x y) then false else true) ys in 
	impl (y::xs) ys
  in (*Debug.debug_ref:=true; *)let xs = impl [] xs in (*Debug.debug_ref:=false;*) xs

(** implements s1 U s2  *)
let rec union_formsets lo s2 s1 =
(*  compact_formset lo (s2@s1)*)
  match s1 with 
  | [] -> s2
  | s::s1' -> 
      if (formset_mem lo s s2) then 
	union_formsets lo s2 s1'  
      else s::(union_formsets lo s2 s1') 
