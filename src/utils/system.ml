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
