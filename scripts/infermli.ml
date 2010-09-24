(** Run from the root directory of jStar. *)

let _ =
  let src_dirs = "src" :: Utils.files_map Sys.is_directory (fun x->x) "src" in
  let cmd_prefix = "ocamlbuild -I " ^ String.concat " -I " src_dirs in
  let infer_mli fn =
    let fn = Filename.basename fn in
    let fn = Filename.chop_suffix fn ".ml" in
    ignore (Sys.command (cmd_prefix ^ " " ^ fn ^ ".inferred.mli")) in
  let filter fn =
    Filename.check_suffix fn ".ml" &&
    not (Sys.file_exists (fn ^ "i")) in
  Utils.files_iter filter infer_mli "src"
