(********************************************************
   This file is part of jStar
        src/jimple_syntax/jparsetree.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


type binop =
    And
  | Or
  | Xor
  | Mod
  | Cmp
  | Cmpg
  | Cmpl
  | Cmpeq
  | Cmpne
  | Cmpgt
  | Cmpge
  | Cmplt
  | Cmple
  | Shl
  | Shr
  | Ushr
  | Plus
  | Minus
  | Mult
  | Div
type unop = Lengthof | Neg
type nonstatic_invoke = Special_invoke | Virtual_invoke | Interface_invoke
type identifier = string
type at_identifier = string
type quoted_name = string
type full_identifier = string
type array_brackets = string
type label_name = identifier
type name = Quoted_name of string | Identifier_name of string
val constructor : name -> bool
type class_name =
    Quoted_clname of string
  | Identifier_clname of string
  | Full_identifier_clname of string
type sign = Positive | Negative
type constant =
    Int_const of sign * int
  | Int_const_long of sign * int
  | Float_const of sign * float
  | String_const of string
  | Clzz_const of string
  | Null_const
type immediate =
    Immediate_local_name of name
  | Immediate_constant of constant
type fixed_array_descriptor = immediate
type array_descriptor = immediate option
type j_file_type = ClassFile | InterfaceFile
type modifier =
    Abstract
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
    Boolean
  | Byte
  | Char
  | Short
  | Int
  | Long
  | Float
  | Double
  | Null_type
  | Class_name of class_name
type nonvoid_type =
    Base of j_base_type * array_brackets list
  | Quoted of quoted_name * array_brackets list
  | Ident_NVT of identifier * array_brackets list
  | Full_ident_NVT of full_identifier * array_brackets list
type parameter = nonvoid_type
type parameter_named_option = nonvoid_type * identifier option
type j_type = Void | Non_void of nonvoid_type
type throws_clause = class_name list option
type case_label = Case_label_default | Case_label of sign * int
type declaration = Declaration of j_type option * name list
type case_statement = Case_stmt of case_label * label_name
type method_signature_short = modifier list * j_type * name * parameter list
type method_signature = class_name * j_type * name * parameter list
type field_signature = class_name * j_type * name
type signature =
    Method_signature of method_signature
  | Field_signature of field_signature
type reference =
    Array_ref of identifier * immediate
  | Field_local_ref of name * signature
  | Field_sig_ref of signature
type variable = Var_ref of reference | Var_name of name
type invoke_expr =
    Invoke_nostatic_exp of nonstatic_invoke * name * signature *
      immediate list
  | Invoke_static_exp of signature * immediate list
type expression =
    New_simple_exp of j_base_type
  | New_array_exp of nonvoid_type * fixed_array_descriptor
  | New_multiarray_exp of j_base_type * array_descriptor list
  | Cast_exp of nonvoid_type * immediate
  | Instanceof_exp of immediate * nonvoid_type
  | Binop_exp of binop * immediate * immediate
  | Unop_exp of unop * immediate
  | Invoke_exp of invoke_expr
  | Immediate_exp of immediate
  | Reference_exp of reference
type bool_expr = True | False
type catch_clause =
    Catch_clause of class_name * label_name * label_name * label_name
type extends_clause = class_name list
type implements_clause = class_name list
type list_class_file = ListClassFile of string list
type local_var = j_type option * name
type nodekind =
    Start_node
  | Exit_node
  | Call_node
  | Return_Site_node
  | Stmt_node
val pp_name : Format.formatter -> name -> unit
val pp_class_name : Format.formatter -> class_name -> unit
val pp_inheritance_clause :
  string -> Format.formatter -> class_name list -> unit
val pp_method_signature_short :
  Format.formatter -> 'a * 'b * name * 'c -> unit
