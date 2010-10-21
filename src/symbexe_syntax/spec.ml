(********************************************************
   This file is part of jStar
        src/symbexe_syntax/spec.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** Data structures used to represent specifications.
  Also, their pretty-printing. *)

module ClassMap = Map.Make (struct type t = string let compare = compare end)
module LabelMap = Map.Make (struct type t = string let compare = compare end)

type excep_post = Psyntax.pform ClassMap.t 
type invariants = Psyntax.pform LabelMap.t

type spec = 
    { pre : Psyntax.pform;
      post : Psyntax.pform;
      excep : excep_post;
      invariants : invariants }


let mk_spec pre post excep invariants = 
    { pre = pre;
      post = post;
      excep = excep;
      invariants = invariants }

let spec2str ppf (spec: spec)  = 
  let po s = Format.fprintf ppf "@\n@[<4>{%a}@]" Psyntax.string_form s in
  po spec.pre; po spec.post;
  ClassMap.iter (fun _ s -> po s) spec.excep

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  
let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1
