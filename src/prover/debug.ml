(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)
(*F#
open Microsoft.FSharp.Compatibility
F#*)

let debug_ref = ref true

let debug = !debug_ref

let buffer_dump = Buffer.create 10000
let dump = ref (Format.formatter_of_buffer buffer_dump)


(*IF-OCAML*)
exception Unsupported
let unsupported () = raise Unsupported
(*ENDIF-OCAML*)

(*F#
let unsupported () = failwith "Assert false"
F#*)


let rec list_format sep f ppf list = 
  match list with 
    [] -> Format.fprintf ppf ""
  | [x] -> Format.fprintf ppf "%a" f x 
  | x::xs -> Format.fprintf ppf "@[%a@]%s@ %a" f x sep (list_format sep f) xs 

let toString  f a : string = 
  Format.fprintf (Format.str_formatter) "%a" f a ; Format.flush_str_formatter ()
