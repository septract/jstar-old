(** Functions used by more than one script. *)

(** [files_fold p f init dir] folds over all filenames under [dir]
 * which satisfy [p]. *)
let rec files_fold p f init dir =
  let acc = ref init in
  let sub = Sys.readdir dir in
  for i = 0 to Array.length sub - 1 do begin
    let fn = Filename.concat dir sub.(i) in
    if p fn then acc := f !acc fn;
    if Sys.is_directory fn then acc := files_fold p f !acc fn
  end done;
  !acc
let files_map p f = files_fold p (fun xs y -> f y :: xs) []
let files_iter p f = files_fold p (fun () y -> f y) ()


