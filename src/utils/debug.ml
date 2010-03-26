(********************************************************
   This file is part of jStar 
	src/utils/debug.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(*F#
open Microsoft.FSharp.Compatibility
F#*)

let debug_ref = ref false

let debug = !debug_ref

let buffer_dump = Buffer.create 10000

let flagged_formatter frm flagref = 
  let sxy,fl =  Format.pp_get_formatter_output_functions frm () in 
  Format.make_formatter 
    (fun s x y -> if !flagref then sxy s x y) (fun () -> fl ())

let merge_formatters frm1 frm2 = 
  let sxy1,fl1 =  Format.pp_get_formatter_output_functions frm1 () in 
  let sxy2,fl2 =  Format.pp_get_formatter_output_functions frm2 () in 
  Format.make_formatter (fun s x y -> sxy1 s x y; sxy2 s x y) (fun () -> fl1 () ; fl2 ())



let dump = ref (merge_formatters 
		  (Format.formatter_of_buffer buffer_dump)
		  (flagged_formatter Format.std_formatter debug_ref))

(*IF-OCAML*)
exception Unsupported 
let unsupported () = raise Unsupported

exception Unsupported2 of string 
let unsupported_s s = raise (Unsupported2 s)

(*ENDIF-OCAML*)

(*F#
let unsupported () = failwith "Assert false"
F#*)


let rec list_format sep f ppf list = 
  match list with 
    [] -> Format.fprintf ppf ""
  | [x] -> Format.fprintf ppf "%a" f x 
  | x::xs -> Format.fprintf ppf "@[%a@]@ %s @[%a@]" f x sep (list_format sep f) xs 

let rec list_format_optional start sep f ppf list = 
  match list with 
    [] -> ()
  | x::xs -> Format.fprintf ppf "%s@ @[%a@]" start (list_format sep f) list 

let toString  f a : string = 
  Format.fprintf (Format.str_formatter) "%a" f a ; Format.flush_str_formatter ()
