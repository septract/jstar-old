(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


open Vars
open Pterm
open Plogic
open Rlogic
open Config
open Jparsetree
open Support_syntax
open Jimple_global_types


let file = ref ""

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
  | Identifier_name s -> Arg_var(Vars.concretep_str s)


let identifier2args s = 
    Arg_var(Vars.concretep_str s)


let immediate2args im = 
  match im with 
  | Immediate_local_name n -> name2args n
  | Immediate_constant c -> constant2args c


let reference2args r = (* not sure we need this. Maybe we need reference2PPred*)
  match r with 
  |Array_ref (id,im) -> assert false 
  |Field_local_ref(n,si) -> assert false
  |Field_sig_ref(si) -> assert false

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
  Vars.concretep_str (variable2key v )  


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
    (fun ppf -> List.iter (fun f ->Format.fprintf ppf "@[%a@]@\n " string_ts_form f )) fs


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

let expression2pure e =
  match e with
  | Binop_exp (op,i1,i2) -> bop_to_prover_pred op (immediate2args i1) (immediate2args i2)
  | _ -> Printf.printf "\n\n Expression %s not supported. Abort!" (Pprinter.expression2str e);
      assert false (* ddino: many other cases should be filled in *)			      



(* ================= misc functions =============== *)







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



let this_var_name = Support_syntax.this_var_name

let parameter n = "@parameter"^(string_of_int n)^":"

(* create the "this" *)
let mk_this : Vars.var =
  Vars.concretep_str this_var_name 

(* create the "res" used for the result of traditional assertions *)
let mk_res : Vars.var =
  Vars.concretep_str res_var_name

(* define the constant name for the return variable. *)
(*let name_ret_var mname = (Pprinter.name2str mname)^"$"^"ret_var"*)
let name_ret_var = "$ret_var"

let ret_var = Vars.concretep_str name_ret_var 


let make_field_signature  cname ty n =
  Field_signature(cname,ty,n)
	

