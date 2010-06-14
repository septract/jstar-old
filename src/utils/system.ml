(********************************************************
   This file is part of jStar 
	src/utils/system.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

open Debug

let getenv variable = 
  try Sys.getenv variable 
  with Not_found -> ""


let getenv_dirlist variable = 
  Str.split (Str.regexp ":") (getenv variable)

   
(* read a file into a string *)
let string_of_file fname =
  let ichan = if fname = "-" then stdin else open_in fname
  and str = String.create 1024
  and buf = Buffer.create 1024 in
  let rec loop () =
    let len = input ichan str 0 1024 in
    Buffer.add_substring buf str 0 len;
    if len = 0 then Buffer.contents buf else loop () in
  let s = loop () in
  close_in ichan;
  s



let parse_file pars lexe fname ftype = 
  try 
    if log log_phase then 
      Printf.printf "Start parsing %s in %s...\n" ftype fname;
    let ichan = open_in fname in 
    let ret = pars lexe (Lexing.from_channel ichan) in 
    Parsing.clear_parser ();
    close_in ichan;
    if log log_phase then Printf.printf "Parsed %s!\n" fname;
    ret
  with Parsing.Parse_error -> Printf.printf "Failed to parse %s\n" fname; exit 1
  |  Failure s ->  Printf.printf "Failed to parse %s\n%s\n" fname s; exit 1 





(* 
  Check if file exists in current directory, or in list of directories supplied.  
  Returns full filename if found,
  If not raises Not_found 
*)
let find_file_from_dirs dirs fname =
  if Sys.file_exists fname then fname 
  else 
    let f x = x ^ "/" ^ fname in 
    f (List.find (function d -> Sys.file_exists (f d)) dirs)



let warning () =
  Printf.printf "%c[%d;%dm"  (Char.chr 0x1B ) 1 31

let good () =
  Printf.printf "%c[%d;%dm"  (Char.chr 0x1B ) 1 32 

let reset () =
  Printf.printf "%c[%dm" (Char.chr 0x1B) 0 

