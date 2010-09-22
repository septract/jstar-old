
type vfc_type = 
 | Byte of char 
 | Int of int  
 | Struct of string 
 | Pointer of vfc_type
 | Void_ptr
 | Thread_ptr
 | Array of int 

type op = 
 | PAdd 
 | PSub 
 | Neg
 | Sub
 | Mult
 
type pvar = string * vfc_type

type pexp = 
 | Const of int
 | PVar of pvar
(*| JVar of var*)
 | Prim_op of op * (pexp list) 
 
type field = {
 fname : string; 
 ftype : vfc_type; 
 offset : int; 
}

type stmt = 
 | PVar_decl of pvar 
 | Assign of pvar * pexp 
 | Field_read of pvar * pexp * field 
 | Field_assn of pexp * field * pexp
 | Skip
 | Cond of pexp * stmt * stmt
(*| While of pexp * lexp option * stmt*)
 | While of pexp * stmt
 | Return of pexp option
 | Fun_call of pvar * fun_def * pexp list
 | Block of stmt list 
 | Alloc of pvar * pexp
 | Free of pexp 
 | Fork of pvar * fun_def * pexp list
 | Join of pexp 
 | Get of pexp * pexp * pexp * pexp 
 | Put of pexp * pexp * pexp * pexp 
 | Wait of pexp 

and fun_def = {
  ret_type : vfc_type; 
  params : pvar list; 
(*  requires : lexp; 
  ensures : lexp;  *)
  body : stmt
}

and struct_def = {
  sname : string; 
  fields : field list; 
}

type vfc_decl = 
 | Fun_decl of fun_def
 | Struct_decl of struct_def
 
type vfc_prog = vfc_decl list
