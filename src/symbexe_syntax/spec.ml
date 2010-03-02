module ClassMap =   
  Map.Make(struct
    type t = string
    let compare = compare
  end)


type excep_post = Plogic.pform ClassMap.t 

type spec = 
    { pre : Plogic.pform;
      post : Plogic.pform;
      excep : excep_post }


let mk_spec  pre post excep = 
    { pre=pre;
      post=post;
      excep=excep
    }


let spec2str ppf (spec: spec)  = 
  Format.fprintf ppf "@[{%a}@]@ @[{%a}@]"
    Plogic.string_form spec.pre
    Plogic.string_form spec.post

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  


(* TODO Should add stuff for internal representation of symbolic execution *)
