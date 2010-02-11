open Pprinter
open Pterm
open Plogic
open Methdec_core
open Specification
open Jimple_global_types
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






let spec2str ppf (spec: spec)  = 
  Format.fprintf ppf "@[{%a}@]@ @[{%a}@]"
    string_form spec.pre
    string_form spec.post

let () = pprinter_core_spec2str := ((Debug.toString spec2str) : (spec -> string))
  
  
let variable_list2str lv =
  Debug.list_format "," Vars.pp_var lv

let pp_stmt_core ppf = 
  function
  | Nop_stmt_core -> 
      Format.fprintf ppf "nop;"
  | Label_stmt_core l ->  
      Format.fprintf ppf "%s:" (label_name2str l) 
  | Assignment_core (v,spec,e)-> 
      Format.fprintf ppf "%a@ @[%a@]@[(%a)@];"
	(fun ppf v -> match v with [] -> () | _ -> Format.fprintf ppf "%a@ :=@ " variable_list2str v) v	
	spec2str spec
	string_args_list e
  | Goto_stmt_core l ->
      Format.fprintf ppf 
	"goto %a;"  
	(Debug.list_format "," (fun ppf -> Format.fprintf ppf "%s")) l
  | Throw_stmt_core a -> 
      Format.fprintf ppf 
	"throw %a;"
	string_args a


