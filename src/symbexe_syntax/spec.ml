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
module ClassMap =   
  Map.Make(struct
    type t = string
    let compare = compare
  end)

type excep_post = Psyntax.pform ClassMap.t 

type spec = 
    { pre : Psyntax.pform;
      post : Psyntax.pform;
      excep : excep_post }


let mk_spec  pre post excep = 
    { pre=pre;
      post=post;
      excep=excep
    }

let spec2str ppf (spec: spec)  = 
  Format.fprintf ppf "@[{%a}@]@ @[{%a}@]"
    Psyntax.string_form spec.pre
    Psyntax.string_form spec.post

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  
let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1


(* TODO Should add stuff for internal representation of symbolic execution *)
