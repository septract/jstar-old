(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

(* Types used to parse jimple *)

type binop= And | Or | Xor | Mod | Cmp | Cmpg | Cmpl | Cmpeq 
	    | Cmpne | Cmpgt | Cmpge | Cmplt | Cmple | Shl 
	    | Shr | Ushr | Plus | Minus | Mult |Div  

type unop= Lengthof | Neg

type nonstatic_invoke = 
  | Special_invoke 
  | Virtual_invoke
  | Interface_invoke

type identifier = string
type at_identifier = string

type quoted_name = string 
    
type full_identifier = string

type array_brackets = string

type label_name =  identifier

type name = 
  | Quoted_name of string
  | Identifier_name of string

let constructor name = 
  match name with
    Identifier_name s -> s="<init>"
  | _ -> false


type class_name =
  | Quoted_clname of string
  | Identifier_clname of string
  | Full_identifier_clname of string

(*
type class_file_name = 
  | Cfname of string
*)
type sign = Positive | Negative

type constant=
   | Int_const of sign * int
   | Int_const_long of sign * int
   | Float_const of sign * float
   | String_const of string
   | Clzz_const of string    
   | Null_const    

type immediate = 
  | Immediate_local_name of  name
  | Immediate_constant of  constant

type fixed_array_descriptor =  immediate

type array_descriptor =  immediate option 

type j_file_type = ClassFile | InterfaceFile

type modifier =    
   | Abstract
   | Final
   | Native
   | Public
   | Protected
   | Private
   | Static
   | Synchronized
   | Transient
   | Volatile
   | Strictfp
   | Enum
   | Annotation

type j_base_type =
  | Boolean 
  | Byte 
  | Char 
  | Short 
  | Int 
  | Long 
  | Float 
  | Double 
  | Null_type  
  | Class_name of class_name

(* ddino: to be fixed.... what to do with quoted_name, identifier, full_identifier?? *)
type nonvoid_type =
  | Base of  j_base_type * array_brackets list
  | Quoted of  quoted_name * array_brackets list
  | Ident_NVT of   identifier * array_brackets list
  | Full_ident_NVT of  full_identifier * array_brackets list

type parameter =  nonvoid_type
type parameter_named_option =  nonvoid_type * identifier option

type  j_type = 
  | Void 
  | Non_void of  nonvoid_type

type throws_clause = class_name list option

type case_label = 
  |Case_label_default 
  | Case_label of sign * int 

(* j_type ooption because it can be unknown. see parser *)
type declaration = Declaration of j_type option *  name list




type case_statement = Case_stmt of  case_label *  label_name

type method_signature_short = j_type *  name *  parameter list
type method_signature = class_name * j_type *  name *  parameter list
type field_signature = class_name * j_type *  name

type signature = 
  | Method_signature of method_signature
  | Field_signature of field_signature

type reference = 
  |Array_ref of  identifier *  immediate
  |Field_local_ref of  name *  signature
  |Field_sig_ref of  signature

type variable = 
  | Var_ref of  reference
  | Var_name of  name

type invoke_expr =
  | Invoke_nostatic_exp of nonstatic_invoke * name * signature * immediate list option
  | Invoke_static_exp of signature * immediate list option 



type expression = 
  | New_simple_exp of j_base_type
  | New_array_exp of  nonvoid_type *  fixed_array_descriptor 
  | New_multiarray_exp of j_base_type *  array_descriptor list
  | Cast_exp of  nonvoid_type *  immediate
  | Instanceof_exp of  immediate *  nonvoid_type
  | Binop_exp of  binop *  immediate *  immediate 
  | Unop_exp of  unop *  immediate
  | Invoke_exp of invoke_expr
  | Immediate_exp of immediate
  | Reference_exp of reference

type bool_expr = True | False




type statement = 
   | Label_stmt of  label_name 
   | Breakpoint_stmt
   | Entermonitor_stmt of  immediate
   | Exitmonitor_stmt of  immediate
   | Tableswitch_stmt of  immediate * case_statement list
   | Lookupswitch_stmt of  immediate * case_statement list 
   | Identity_stmt of name * at_identifier * j_type (* ddino: in theory it's local_name,at_identifier *)
   | Identity_no_type_stmt of name * at_identifier (* ddino: in theory it's local_name,at_identifier *)
   | Assign_stmt of variable * expression       
   | If_stmt of expression * label_name 
   | Goto_stmt of label_name  
   | Nop_stmt
   | Ret_stmt of immediate option
   | Return_stmt of immediate option
   | Throw_stmt of immediate
   | Invoke_stmt of invoke_expr       

type declaration_or_statement =
  |  DOS_dec of declaration
  |  DOS_stm of statement


type  catch_clause = Catch_clause of class_name * label_name * label_name * label_name

(*type  method_body = (declaration list * statement list * catch_clause list) option  *)

type  method_body = (declaration_or_statement list * catch_clause list) option  

type  member = 
  | Field of  modifier list * j_type *  name
  | Method of  modifier list * j_type * name * parameter list * throws_clause * method_body
      
type extends_clause = class_name option

type implements_clause = (class_name list) option

type jimple_file = 
  | JFile of modifier list * j_file_type * class_name * extends_clause * implements_clause * (member list)

type list_class_file = 
  | ListClassFile of  string  list

(* ==================   ================== *)


type local_var = j_type option * name 

type stmt = { 
  (*labels: labels; *)
  mutable skind: statement;
  mutable sid: int;  (* this is filled when the cfg is done *)
  mutable succs: stmt list; (* this is filled when the cfg is done *)
  mutable preds: stmt list  (* this is filled when the cfg is done *)
 }

type methdec = {
 modifiers: modifier list;
 class_name: class_name;
 ret_type:j_type;
 name: name; 
 params: parameter list; 
 locals: local_var list;
 th_clause:throws_clause;
 mutable bstmts: stmt list; (* this is set after the call of cfg *)
}



(* ==================   ================== *)



