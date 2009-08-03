open Jparsetree
open Plogic

let bop_to_prover_arg = function
      |	And -> "builtin_and"
      | Or -> "builtin_or"
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
