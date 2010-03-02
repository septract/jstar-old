open Jparsetree

(***************************************************
 from jparsetree
***************************************************)

type pterm_args = 
  | Arg_var of Vars.var
  | Arg_string of string
  | Arg_op of string * pterm_args list
  | Arg_cons of string * pterm_args list  (* Do not use *)
  | Arg_record of (string *  pterm_args) list (* Do not use *)

type plogic_pform_at =
  | P_EQ of pterm_args * pterm_args
  | P_NEQ of pterm_args * pterm_args
  | P_PPred of string * pterm_args list
  | P_SPred of string * pterm_args list 
  | P_Wand of plogic_pform * plogic_pform
  | P_Or of plogic_pform * plogic_pform
  | P_Septract of plogic_pform * plogic_pform
  | P_Garbage
  | P_False
and plogic_pform = plogic_pform_at list

module Specification_ClassMap =   
  Map.Make(struct
    type t = string
    let compare = compare
  end)

type specification_excep_post = plogic_pform Specification_ClassMap.t 
type specification_spec = 
    { pre : plogic_pform;
      post : plogic_pform;
      excep : specification_excep_post }

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
	 | Spec_stmt of Vars.var list * specification_spec

type declaration_or_statement =
  |  DOS_dec of declaration
  |  DOS_stm of statement

type  method_body = (declaration_or_statement list * catch_clause list) option  

type requires_clause = method_body

type old_clauses = method_body list

type ensures_clause = method_body

type  member = 
  | Field of  modifier list * j_type *  name
  | Method of  modifier list * j_type * name * parameter list * throws_clause * requires_clause * old_clauses * ensures_clause * method_body

type jimple_file = 
  | JFile of modifier list * j_file_type * class_name * extends_clause * implements_clause * (member list)


type methdec_jimple = {
 modifiers: modifier list;
 class_name: Jparsetree.class_name;
 ret_type:j_type;
 name_m: name; 
 params: parameter list; 
 locals: local_var list;
 th_clause:throws_clause;
 req_locals: local_var list; (* local variables of the requires clause *)
 mutable req_stmts: statement list; (* the requires clause statements *)
 mutable old_stmts_list: statement list list; (* the old statements. Their locals are contained in ens_locals *)
 ens_locals: local_var list; (* local variables of the ensures clause and old clauses *)
 mutable ens_stmts: statement list; (* the ensures clause statements *)
 mutable bstmts: statement list; (* this is set after the call of cfg *)
}
