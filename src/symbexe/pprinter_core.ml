open Global_types
open Pprinter
open Pterm
open Plogic
open Spec_def
(* =================== PPrinter for core  ============================ *)

let rec args2str  arg = 
  match arg with 
  | Arg_var v -> Vars.string_var v
  | Arg_string s -> s 
  | Arg_op ("builtin_plus",[a1;a2]) ->  "("^(args2str a1)^"+"^(args2str a2)^")"
  | Arg_op (name,args) ->  name^"("^( args_list2str args)^")" 
  | Arg_cons (name,args) -> name^"("^( args_list2str args)^")" 
  | Arg_record fldlist -> "[{"^(args_fldlist2str fldlist)^"}]"
and args_list2str argsl = 
  match argsl with 
  | [] -> ""
  | [a] ->  args2str a
  | a::al ->  (args2str a)^","^(args_list2str al)
and args_fldlist2str fdl =  
  match fdl with 
  | [] ->  ""
  | [(f,a)] -> f^"="^( args2str a)
  | (f,a)::fdl -> f^"="^(args2str a)^"; "^(args_fldlist2str fdl)



let rec form_at2str pa =  
  match pa with 
    P_NEQ(a1,a2) ->(args2str a1)^ "!= "^  (args2str a2)
  | P_EQ(a1,a2) ->  (args2str a1)^ " = "^ (args2str a2)
  | P_PPred(op,al) -> op^"("^ (args_list2str al)^")"
  | P_SPred (s,al) -> s^"("^ (args_list2str al)^")"
  | P_Or(f1,f2) -> "[[("^(list_form2str f1)^" || "^" [("^( list_form2str f2)^")]]"
  | P_Wand(f1,f2) -> "[[("^(list_form2str f1)^" -* "^" [("^( list_form2str f2)^")]]"
  | P_Septract(f1,f2) ->  "[[("^(list_form2str f1)^" -o "^" [("^( list_form2str f2)^")]]"
  | P_False ->  "False"
  | P_Garbage ->  "Garbage"
and list_form2str  list = 
  match list with 
    [] ->  ""
  | [x] ->  (form_at2str x)
  | x::xs -> (form_at2str x)^" * "^list_form2str  xs 






let spec2str (spec: Spec_def.spec) : string = 
  let f p =
    match p with 
    |[]->""
    |[p'] -> form_at2str p'
    | _ -> list_form2str p 
  in
  "{"^(f spec.pre)^"}{"^(f spec.post)^"}"
  
let rec variable_list2str lv =
  match lv with
  | [] -> ""
  | [v] -> variable2str v
  | v::lv' -> (variable2str v)^","^ (variable_list2str lv') 

let rec immediate_list2str il =
  match il with
  | [] -> ""
  | [i] -> immediate2str i
  | i::il' -> (immediate2str i)^","^ (immediate_list2str il') 

let statement_core2str = function
  | Nop_stmt_core -> "nop;"
  | Label_stmt_core l ->  label_name2str l ^":"
  | Assignment_core (v,spec,Some e)-> (variable_list2str v)^":= "^(spec2str spec)^"("^(immediate_list2str e)^")"
  | Assignment_core (v,spec,None)-> (variable_list2str v)^":= "^(spec2str spec)^"()"
  | If_stmt_core (e,l) -> "if "^ expression2str e ^" goto "^ label_name2str l 
  | Goto_stmt_core l ->"goto "^label_name2str l^";"   
  | Throw_stmt_core i -> "throw "^immediate2str i^";"

