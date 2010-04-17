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
  Format.fprintf ppf "@[<2>{%a}@]@\n@[<2>{%a}@]"
    Psyntax.string_form spec.pre
    Psyntax.string_form spec.post;
  ClassMap.iter 
    (fun cn pf -> Format.fprintf ppf " @[{%a}@]" Psyntax.string_form pf)
    spec.excep

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  


(* TODO Should add stuff for internal representation of symbolic execution *)
