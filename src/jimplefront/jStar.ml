(********************************************************
   This file is part of jStar
        src/jimplefront/jStar.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(**
  This aims to become the command-line interface of the Java frontend. For
  now, it processes Java through jimple, which explains the location. The
  file should be moved once Java is handled directly.
 *)

open Format
open Jstar_std
open Scanf

module JPT = Jparsetree

(* {{{ module Path *)
(** Functions that deal with Java CLASSPATHs and SOURCEPATHs. *)
(* TODO(rgrig): Should CLASSPATH and SOURCEPATH be treated differently? *)
module Path : sig
  (** A classpath. *)
  type t

  (** 
    Understands any Java CLASSPATH. The path separator is system dependent.
    Leading, trailing, and repeated separators are ignored. Paths DIR/* are
    equivalent to specifying all JAR files in DIR, without any guarantees
    on the order. Entries that aren't accessible directories or JAR/ZIP
    files are silently ignored. Note that all this is standard java/javac
    behavior.
   *)
  val of_string : string -> t

  (** 
    Returns a CLASSPATH in which (1) no entry is duplicated, (2) entries
    are accessible by the running program, (3) each entry is either a
    directory or a JAR/ZIP, (4) the CLASSPATHs in JARs' META files are
    explicitely expanded.
   *)
  val to_string : t -> string

  (** [prepend p cp] returns an equivalent of "p:cp". *)
  val prepend : string -> t -> t

  (** [is_empty cp] returns whether the classpath [cp] is empty. *)
  val is_empty : t -> bool

  (** 
    [md5_of_class cp cn] searches for class [cn] in the classpath [cp] and
    returns a hex MD5 hash of its bytecode. If the class is not in the
    classpath it throws [Not_found]. Unfortunatelly, this loads the whole
    bytecode in memory.
   *)
  val md5_of_class : t -> string -> string
end = struct
  type t = string list

  (* Monad operation for lists. *)
  let ( >>= ) l f = List.concat (List.map f l)

  let is_jar fn = System.is_file ".jar" fn || System.is_file ".zip" fn
  let is_directory d = Sys.file_exists d && Sys.is_directory d
  let get_jars d =
    try 
      Sys.readdir d |> 
      Array.to_list |> 
      List.map (Filename.concat d) |>
      List.filter is_jar
    with Sys_error _ -> []

  let add h p =
    (* TODO(rgrig): Is there a better way to normalize the file name? *)
    let p = Filename.concat (Filename.dirname p) (Filename.basename p) in
    let r = Hashtbl.mem h p in
    if not r then Hashtbl.replace h p p;
    not r

  let read_classpath =
    let line_glue = Str.regexp "[\r\n]+ +" in
    let cp_pattern = Str.regexp "^Class-Path: *\\(\\(.*[\r\n]+ +\\)*.*\\)$" in
    let path_separator = Str.regexp " " in
    fun fn ->
    try
      let jar = Zip.open_in fn in
      let manifest_entry = Zip.find_entry jar "META-INF/MANIFEST.MF" in
      let manifest = Zip.read_entry jar manifest_entry in
      let _ = Str.search_forward cp_pattern manifest 0 in
      let cp = Str.matched_group 1 manifest in
      let cp = Str.global_replace line_glue "" cp in
      let cp = Str.split path_separator cp in
      let cp = List.map (Filename.concat (Filename.dirname fn)) cp in
      Zip.close_in jar; cp
    with 
      | Zip.Error _ | Not_found -> [] (* Silenty ignore, like java does. *)
      | _ -> failwith "Unexpected exception in Path.read_classpath"

  let rec expand seen p = 
    if StringH.ends_with "*" p then
      (get_jars (Filename.dirname p) >>= expand seen)
    else if is_directory p && add seen p then 
      [p]
    else if is_jar p && add seen p then 
      (p :: (read_classpath p >>= expand seen))
    else
      []

  let of_string s =
    Str.split System.java_path_delimiter_re s >>= expand (Hashtbl.create 101)

  let to_string = 
    String.concat System.java_path_delimiter

  let is_empty = ( <> ) []

  let prepend p cp =
    let seen = Hashtbl.create (2 * List.length cp + 1) in
    let rec unique acc = function
      | [] -> List.rev acc
      | p :: ps -> unique (if add seen p then p :: acc else acc) ps in
    unique (expand seen p) cp

  let fn_of_cn cn =
    (Str.split (Str.regexp "\\.") cn |> List.fold_left Filename.concat "")
    ^ ".class"

  let md5_of_class' cp cn =
    let fn = fn_of_cn cn in
    let read_from_jar jar =
      let jar = Zip.open_in jar in
      let entry = Zip.find_entry jar fn in
      let r = Zip.read_entry jar entry in
      Zip.close_in jar; r in
    let read_from_dir dir =
      System.string_of_file (Filename.concat dir fn) in
    let md5 p =
      (if is_jar p then read_from_jar else read_from_dir) p |>
      Digest.string |> Digest.to_hex in
    Misc.map_and_find md5 cp

  let md5_of_class = Misc.memo2 md5_of_class'
end
(* }}} *)
(* {{{ module Cli *)
(**
  Parses command lines similarly with javac. Commands <tt>javac ARGS</tt>
  should still work as <tt>jStar ARGS</tt> when ARGS does not contain class
  names; anything else is a bug in this module. A few options of javac are
  interpreted and most are silently ignored. In fact, anything that starts
  with '-' and is not a recognized option is silently ignored, such that
  future options of javac don't require us to update this module.

  There are many commands <tt>jStar ARGS</tt> that do not work when
  converted to <tt>javac ARGS</tt>. A trivial example is <tt>jStar
  -foobar</tt>, where 'foobar' is not an option recognized by javac, but
  is ignored by jStar. More interestingly, there are arguments interpreted
  by jStar, which javac does not understand. These include files with the
  extension ".spec", files with the extension ".rule", and the option
  "-specpath".
 *)
(* TODO(rgrig): Add -fast switch, to assume p/C.java contains class p.C. *)
module Cli : sig
  exception Invalid_cli

  val nowarn : bool ref
  val verbose : bool ref
  val classpath : Path.t ref
  val sourcepath : Path.t ref
  val specpath : Path.t ref
  val java_files : string list ref
  val spec_files : string list ref
  val rule_files : string list ref
  val classes : string list ref

  val parse : string array -> unit

  val dump : formatter -> unit (* for debug *)
end = struct
  (* IMPLEMENTATION.
    The implementation does not use the standard module [Arg] because it
    is a bit too inflexible. For example, the only way to ignore options
    (starting with '-') is to add them to the spec list with a do-nothing
    handler. But then they are printed whenever help is requested. An also,
    if an option is added to javac, then it must also be added here. Another
    problem is that "--help" is an argument no matter what, while javac
    does not recognize it. Another problem is that there seems to be no easy
    way to support the "@file" arguments of javac. And so on.

    The main function below is [parse_stream]. A 'stream' is a function
    [get_arg : unit -> string option] that returns the next argument to
    process as long as there is one. To each argument [parse_stream] tries
    to apply handlers from a list until one returns [true], saying that it
    id handle the argument. All handlers are used when the command line is
    processed ([command_line_arg_handlers]), but [at_handler] is ommited
    while processing a file with arguments, so that javac's behavior is
    immitated. (That behavior is probably intended to avoid inclusion
    cycles.)
   *)

  (* TODO(rgrig): Is it better to use [Stream] from stdlib? *)

  exception Invalid_cli

  let version = "0.2" (* TODO(rgrig): move *)

  let nowarn = ref false
  let verbose = ref false
  let java_files = ref []
  let spec_files = ref []
  let rule_files = ref []

  let classpath = ref (Path.of_string ".")
  let sourcepath = ref (Path.of_string "")
  let specpath = ref (Path.of_string "")
  
  let classes = ref []

  let dump ppf =
    let ps ppf s = fprintf ppf "@ %s" s in
    let pl tag = fprintf ppf "@[<2>%s=%a@]@\n" tag (Debug.pp_list ps) in
    let pp tag p = fprintf ppf "@[<2>%s=%s@]@\n" tag (Path.to_string p) in
    fprintf ppf "@[<2>(command line@\n";
    fprintf ppf "nowarn=%b@\nverbose=%b@\n" !nowarn !verbose;
    pl "classes" !classes;
    pl "java_files" !java_files;
    pl "spec_files" !spec_files;
    pl "rule_files" !rule_files;
    pp "classpath" !classpath;
    pp "sourcepath" !sourcepath;
    pp "specpath" !specpath;
    fprintf ppf ")@]@\n"

  let program_name = ref ""

  (* These are javac's options that take an argument and we ignore. *)
  let kw2 =
    let h = Hashtbl.create 101 in
    List.iter (fun x -> Hashtbl.replace h x ()) [
      "-bootclasspath";
      "-extdirs";
      "-endorsedirs";
      "-processor";
      "-processorpath";
      "-d";
      "-s";
      "-encoding";
      "-source";
      "-target";
      "-Xmaxerrs";
      "-Xmaxwarns";
      "-Xstdout"];
    h

  type spec =
    | Bool of bool ref
    | Path of Path.t ref
    | Act of (unit -> unit)

  let print_usage () =
    eprintf "@[Usage: %s <options> <source files> <classes>@." !program_name

  let print_args speclist =
    let suffix = function
      | Path _ -> " <path>"
      | _ -> "" in
    let len (s, t, _) = String.length s + String.length (suffix t) in
    let max_sz = List.fold_left max 0 (List.map len speclist) in
    let print_one (arg, t, descr) =
      eprintf "@[<4>  %s%s" arg (suffix t);
      for i = len (arg, t, descr) to max_sz do eprintf " " done;
      eprintf "%s@]@." descr in
    List.iter print_one speclist

  let rec speclist =
    let cp_desc = "Specify where to find user class files" in [
    ("-nowarn", Bool nowarn, "Generate no warnings");
    ("-verbose", Bool verbose,
      "Output messages about what the verifier is doing");
    ("-classpath", Path classpath, cp_desc);
    ("-cp", Path classpath, cp_desc);
    ("-sourcepath", Path sourcepath,
      "Specify where to find input source files");
    ("-specpath", Path specpath,
      "Specify where to find spec files and rule files");
    ("-version",
      Act (fun () -> eprintf "@[%s %s@." !program_name version),
      "Version information");
    ("-help",
      Act (fun () -> print_usage (); print_args speclist),
      "Print a synopsys of standard options")]

  let spechash =
    let h = Hashtbl.create 13 in
    List.iter (fun (s, f, _) -> Hashtbl.add h s f) speclist; h

  type error =
    | Missing_arg of string
    | Missing_file of string

  exception Error of error

  let report_error e =
    eprintf "@[<2>%s: " !program_name;
    (match e with
      | Missing_arg x -> eprintf "%s requires an argument@." x
      | Missing_file x -> eprintf "file not found: %s@." x);
    print_usage ();
    eprintf "@[use -help for a list of possible options@."

  let is_optionlike = StringH.starts_with "-"

  let rec parse_one arg get_arg = function
    | [] -> failwith "Handlers should cover all cases."
    | h :: hs -> if not (h arg get_arg) then parse_one arg get_arg hs

  let rec parse_stream get_arg handlers =
    match get_arg () with
      | None -> ()
      | Some arg ->
          parse_one arg get_arg handlers; parse_stream get_arg handlers

  let handle_known_options arg get_arg =
    try
      (match Hashtbl.find spechash arg with
        | Bool b -> b := true
        | Path p ->
            (match get_arg () with
              | None -> raise (Error (Missing_arg arg))
              | Some v -> p := Path.of_string v)
        | Act f -> f ());
      true
    with Not_found -> false

  let ignore_args_of_kw2 arg get_arg =
    if Hashtbl.mem kw2 arg then (ignore (get_arg ()); true) else false

  let ignore_options arg _ = is_optionlike arg

  let handle_files arg _ =
    (if Filename.check_suffix arg ".java" then java_files
    else if Filename.check_suffix arg ".spec" then spec_files
    else if Filename.check_suffix arg ".rule" then rule_files
    else classes) =:: arg; true

  let file_arg_handlers = [
    handle_known_options;
    ignore_args_of_kw2;
    ignore_options;
    handle_files]

  let at_handler arg _ =
    let n = String.length arg in
    if n = 0 || arg.[0] <> '@' then false
    else begin
      let arg = String.sub arg 1 (n - 1) in begin
        try
          let arg_file = open_in arg in
          try
            let lexbuf = Lexing.from_channel arg_file in
            let get_arg () = Arg_file_lexer.arg lexbuf in
            parse_stream get_arg file_arg_handlers;
            close_in arg_file
          with e -> close_in_noerr arg_file; raise e
        with Sys_error _ -> raise (Error (Missing_file arg))
      end;
      true
    end

  let command_line_arg_handlers = at_handler :: file_arg_handlers

  let set_defaults () =
    let sp l e d = 
      l := Path.of_string (try Sys.getenv e with Not_found -> d) in
    sp classpath "CLASSPATH" ".";
    sp sourcepath "SOURCEPATH" "";
    sp specpath "SPECPATH" ""

  let check_files lst =
    try 
      let f = List.find (not @@ System.is_file "") lst in 
      raise (Error (Missing_file f))
    with Not_found -> ()

  let rec parse argv =
    try
      let n = Array.length argv in
      if n = 1 then parse (Array.of_list [argv.(0); "-help"])
      else begin
        set_defaults (); program_name := argv.(0);
        parse_stream
          (let i = ref 0 in fun () -> (* this skips argv.(0) *)
            incr i; if !i < n then Some argv.(!i) else None)
          command_line_arg_handlers;
        check_files (!java_files @ !spec_files @ !rule_files)
      end
    with Error e -> report_error e; raise Invalid_cli
end
(* }}} *)
(* {{{ module JimpleCache *)
(**
  Keeps information about which classes have up to date jimple files, and
  persists it to disk. Instead of timestamps, this module uses MD5 hashes.
  This way (1) if a class file is moved and the classpath updated it needs
  not be recompiled and (2) we need not worry about {b javac} touching
  classes without changing them.
 *)
module JimpleCache : sig
  (** The type of a cache. *)
  type t

  (** 
    [load dir cp] loads the jimple cache in [dir] and remembers to do all
    later class lookups using [cp]. If [dir] does not contain a jimple
    cache, then an empty one is returned.
   *)
  val load : string -> Path.t -> t

  (** [save cache] saves [cache].  *)
  val save : t -> unit

  (** [has cache cn] says if we have jimple for class [cn]. *)
  val has : t -> string -> bool

  (** 
    [update cache cns] records that jimple for classes [cns] was
    recomputed.
   *)
  val update : t -> string list -> unit
end = struct
  type classinfo = {
    class_md5 : string;
    jimple_md5 : string
  }

  type t = {
    classes : (string, classinfo) Hashtbl.t; (* this is persisted *)
    classpath : Path.t;
    directory : string
  }

  let cache_index dir = Filename.concat dir "index"

  let load dir cp =
    let h = Hashtbl.create 101 in
    (try
      let cache_file = open_in (cache_index dir) in
      try while true do
        fscanf cache_file "%s %s %s " 
          (fun ch jh cn -> Hashtbl.replace h cn {class_md5=ch; jimple_md5=jh})
      done with End_of_file -> close_in_noerr cache_file
    with Sys_error _ -> ());
    { classes = h; classpath = cp; directory = dir }

  let save cache =
    System.mkdir_p cache.directory;
    let out = open_out (cache_index cache.directory) in
    let print_entry cn { class_md5=class_md5; jimple_md5=jimple_md5 } =
      Printf.fprintf out "%s %s %s\n" class_md5 jimple_md5 cn in
    Hashtbl.iter print_entry cache.classes;
    Printf.fprintf out "%!";
    close_out_noerr out

  let md5_of_jimple cache cn =
    Filename.concat cache.directory (cn ^ ".jimple") |>
    Digest.file |> Digest.to_hex
  
  let has cache cn =
    try
      let ci = Hashtbl.find cache.classes cn in
      Path.md5_of_class cache.classpath cn = ci.class_md5 &&
      md5_of_jimple cache cn = ci.jimple_md5
    with _ -> false

  let update cache cns =
    let update_one cn =
      try Hashtbl.replace cache.classes cn 
        { class_md5 = Path.md5_of_class cache.classpath cn;
          jimple_md5 = md5_of_jimple cache cn }
      with _ -> () in
    List.iter update_one cns
end
(* }}} *)
(* {{{ errors and warnings *)
type error =
  | Not_in_path of string
  | Subtool of string
  | Unset_soot_jar

let report_error e = 
  eprintf "@[<2>ERROR: "; 
  begin
    match e with
    | Not_in_path x -> eprintf "%s not in PATH" x
    | Subtool x -> eprintf "Reported by %s" x
    | Unset_soot_jar -> eprintf "SOOT_JAR is unset"
  end;
  eprintf "@."

exception Error of error

type warning =
  | Guessed_soot_jar of string

let warn w =
  if not !Cli.nowarn then begin
    eprintf "@[<2>Warning: ";
    begin
      match w with
        | Guessed_soot_jar x -> eprintf "I'm guessing SOOT_JAR=%s" x
    end;
    eprintf "@."
  end
(* }}} *)
(* {{{ constants *)
(* [rm work_dir] should clean all files generated by jStar. *)
let ( / ) = Filename.concat
let work_dir = "jstar.out"
let jimple_dir = work_dir/"jimple"
let classes_dir = work_dir/"classes"
let specs_dir = work_dir/"specs" (* specs from Java @Annot *)
let log_dir = work_dir/"log"
(* }}} *)
(* {{{ helpers *)
let check_executables =
  List.iter
    (fun x -> if not (System.is_executable_available x) 
      then raise (Error (Not_in_path x)))

let guess_soot_jar () =
  if List.mem Sys.os_type ["Unix"; "Cygwin"] then begin
    let o, i, e = (* capture stderr too *)
      Unix.open_process_full
        "locate soot | grep /soot-.*\\\\.jar$"
        (Array.make 0 "") in
    let l = try input_line o with _ -> "" in
    if System.is_file ".jar" l then Some l else None
  end else None (* TODO(rgrig): guessing on windows *)

let get_soot_jar () =
  let soot_jar = System.getenv "SOOT_JAR" in
  if not (System.is_file ".jar" soot_jar) then begin
    match guess_soot_jar () with
      | Some x -> (warn (Guessed_soot_jar x); x)
      | None -> raise (Error Unset_soot_jar)
  end else soot_jar

(* TODO(rgrig): Should I set -s to something under jstar.out? *)
let get_javac_cmd cp sp jf =
  Array.of_list &
    ["javac"; "-d"; classes_dir] @
    (if Path.is_empty cp then ["-cp"; Path.to_string cp] else []) @
    (if Path.is_empty sp then ["-sp"; Path.to_string sp] else []) @
    jf

let get_soot_cmd cp classes = 
  Array.of_list &
    ["java"; "-jar"; get_soot_jar (); "-cp"; 
    Path.to_string (Path.prepend classes_dir cp); "-pp"; "-f"; "J";
    "-d"; jimple_dir] @ classes

(* TODO(rgrig): Move in System? *)
let print_file f fn =
  let chunk_size = 1024 in
  let buf = String.create chunk_size in
  let fc = open_in fn in
  let rec loop () =
    let sz = input fc buf 0 chunk_size in
    fprintf f "%s" (if sz = chunk_size then buf else String.sub buf 0 sz);
    if sz <> 0 then loop () in
  fprintf f "@["; loop (); fprintf f "@.";
  close_in_noerr fc

let make_empty_file rw name =
  let path = work_dir / name in
  path, Unix.openfile path [rw; Unix.O_CREAT; Unix.O_TRUNC] 0o644

(* 
  This runs a tool giving it an empty stdin. The output of the tool is
  hidden unless the exit code is nonzero, in which case both the stdout and
  the stderr of the tool are printed and then [Subtool t] is raised. The
  implementation redirects the output of the tool to files; an alternative
  would be to use pipes with [select] (but doesn't work on windows) or with
  threads (somewhat heavyweight). (Note that pipes without either select or
  threads may fill and deadlock.)
 *)
(* TODO(rgrig): Check that on win/cygwin the child dies on sigint. *)
(* TODO(rgrig): Nice error on file create/read/close problems. *)
let run tool_name command =
  if !Cli.verbose then begin
    printf "@[<2>running"; Array.iter (printf "@ %s") command; printf "@."
  end;
  let out_path, out = make_empty_file Unix.O_WRONLY (tool_name ^ ".out") in
  let err_path, err = make_empty_file Unix.O_WRONLY (tool_name ^ ".err") in
  let _, empty_in = make_empty_file Unix.O_RDONLY (tool_name ^ ".in") in
  let tool_pid = Unix.create_process command.(0) command empty_in out err in
  match Unix.waitpid [] tool_pid with
    | _, Unix.WEXITED 0 -> List.iter Unix.close [out; err; empty_in]
    | _ -> List.iter Unix.close [out; err; empty_in];
        List.iter (print_file err_formatter) [out_path; err_path];
        raise (Error (Subtool tool_name))

let cn_of_fn fn =
  let rec go acc prefix =
    if prefix = classes_dir then String.concat "." acc
    else go (Filename.basename prefix :: acc) (Filename.dirname prefix) in
  go [] (Filename.chop_suffix fn ".class")
(* }}} *)
(* {{{ *) (** {2 main phases} *)
(* 
  Returns the classes defined in [java_files], and makes sure their
  bytecode is in [classes_dir]. Note that A.java may define class B, while
  B.java defines class A.
 *)
let compile_java_to_class class_path source_path java_files =
  if java_files <> [] then begin
    let start_time = (* The filesystem might be on another machine. *)
      let f = work_dir / "javac_starttime" in
      (f |> open_out |> close_out); (* TODO(rgrig): Treat exceptions. *)
      (Unix.stat f).Unix.st_mtime in
    run "javac" (get_javac_cmd class_path source_path java_files);
    let is_generated_class f = 
      System.is_file ".class" f && start_time <= (Unix.stat f).Unix.st_mtime in
    System.fs_filter is_generated_class classes_dir |> List.map cn_of_fn
  end else []

let compile_class_to_jimple class_path classes =
  if classes <> [] then run "soot" (get_soot_cmd class_path classes)

let load_rule_file f =
  printf "@[TODO: load_rule_file %s@." f

let load_spec_file f =
  printf "@[TODO: load_spec_file %s@." f

let _ = object 
  inherit [StringSet.t] Jimple_evaluator.evaluator StringSet.empty
  method eval_class_name = function
    | JPT.Quoted_clname cn
    | JPT.Identifier_clname cn
    | JPT.Full_identifier_clname cn -> StringSet.singleton cn
  method combine = StringSet.union
end

let verify_class c =
  printf "@[TODO: verify_class %s@." c
  (* TODO: (see Run_parser.main)
    - load the jimple
    - make a list with all mentioned classes
    - light-load mentioned classes, for inheritance info and other interface
    - load specs of [c] and of mentioned classes
    - load logics and abstraction rules specific to the mentioned classes
    - construct updated logics, based on specs, and check that specs are OK
    - run symbolic execution
   *)
(* }}} *)
(* {{{ main *)
let _ =
  try
    Cli.parse Sys.argv;
    List.iter load_rule_file !Cli.rule_files;
    List.iter load_spec_file !Cli.spec_files;
    List.iter System.mkdir_p [jimple_dir; classes_dir; specs_dir; log_dir];
    let classes_in_java = 
      compile_java_to_class !Cli.classpath !Cli.sourcepath !Cli.java_files in
    let all_classes = !Cli.classes @ classes_in_java in
    compile_class_to_jimple !Cli.classpath all_classes;
    List.iter verify_class all_classes
  with 
    | Error e -> report_error e
    | Cli.Invalid_cli -> ()
(* }}} *)
