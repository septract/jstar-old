(********************************************************
   This file is part of jStar
        src/utils/cli_utils.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

let ( / ) a b = if Filename.is_relative b then Filename.concat a b else b

let jstar_executable = Sys.executable_name (* This is bit of a guess. *)
let jstar_bin_dir = Filename.dirname jstar_executable
let jstar_home = jstar_bin_dir/Filename.parent_dir_name

(* TODO(rgrig): Ideally [env_var] should be computed from [default]. *)
let library_dirs env_var default = 
  System.getenv_dirlist env_var @ [jstar_home/"library"/default]

let logic_dirs = library_dirs "JSTAR_LOGIC_LIBRARY" "logic"
let specs_dirs = library_dirs "JSTAR_SPECS_LIBRARY" "specifications"
let abs_dirs = library_dirs "JSTAR_ABS_LIBRARY" "abstraction"

(* DBG
let pd a = List.iter (fun x->Printf.printf "dir %s\n" x) a; print_newline ()
let _ = List.iter pd [logic_dirs; specs_dirs; abs_dirs]
*)
