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
  


(* TODO Should add stuff for internal representation of symbolic execution *)
