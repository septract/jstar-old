(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)

type var =
  | PVar of int * string
  | EVar of int * string
  | AnyVar of int * string 

let gensym = ref (0)

let freshe () = 
  gensym := !gensym + 1;
  EVar(!gensym,"v")

let freshp () = 
  gensym := !gensym + 1;
  PVar(!gensym,"v")

let fresha () = 
  gensym := !gensym + 1;
  AnyVar(!gensym,"v")

let freshe_str vn = 
  gensym := !gensym + 1;
  EVar(!gensym,vn)

let freshp_str vn = 
  gensym := !gensym + 1;
  PVar(!gensym,vn)

let concretep_str vn = 
  PVar(0,vn)

let concretee_str vn = 
  EVar(0,vn)


let fresha_str vn = 
  gensym := !gensym + 1;
  AnyVar(!gensym,vn)

let freshen var = 
  match var with 
    PVar (i,v) -> freshp_str v
  | EVar (i,v) -> freshe_str v
  | AnyVar (i,v) -> fresha_str v 


let foo n = if n = 0 then Printf.sprintf "" else Printf.sprintf "_%d" n 

let rec string_var v =
  match v with 
    PVar (n,vn) -> Printf.sprintf  "%s%s" vn (foo n)
  | EVar (n,vn) -> Printf.sprintf  "_%s%s" vn (foo n)
  | AnyVar (n,vn) -> Printf.sprintf  "a_%s%s" vn (foo n)




