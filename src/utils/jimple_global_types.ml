open Jparsetree

(***************************************************
 from jparsetree
***************************************************)


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

type  method_body = (declaration_or_statement list * catch_clause list) option  

type  member = 
  | Field of  modifier list * j_type *  name
  | Method of  modifier list * j_type * name * parameter list * throws_clause * method_body

type jimple_file = 
  | JFile of modifier list * j_file_type * class_name * extends_clause * implements_clause * (member list)


 
type stmt_jimple = { 
  (*labels: labels; *)
  mutable skind: statement;
  mutable sid: int;  (* this is filled when the cfg is done *)
  mutable succs: stmt_jimple list; (* this is filled when the cfg is done *)
  mutable preds: stmt_jimple list  (* this is filled when the cfg is done *)
 }

type methdec_jimple = {
 modifiers: modifier list;
 class_name: Jparsetree.class_name;
 ret_type:j_type;
 name_m: name; 
 params: parameter list; 
 locals: local_var list;
 th_clause:throws_clause;
 mutable bstmts: stmt_jimple list; (* this is set after the call of cfg *)
}
