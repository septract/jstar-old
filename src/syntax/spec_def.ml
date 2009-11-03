open Jparsetree
open Vars
(*open Rterm *)
open Pterm
open Plogic 
open Rterm
open Rlogic
open Prover

module ClassMap =   
  Map.Make(struct
    type t = class_name
    let compare = compare
  end)

type excep_post = Plogic.pform ClassMap.t 
type spec = 
    { pre : Plogic.pform;
      post : Plogic.pform;
      excep : excep_post }

type methodspec =
      Dynamic of method_signature_short * (spec list)
  |   Static of method_signature_short * (spec list)

type methodspecs =
    methodspec list

type apf_define = (string * var * fldlist * Plogic.pform * bool)

type apf_defines = apf_define list

type class_spec = (class_name * apf_defines * methodspecs)

type spec_file = class_spec list 


let mk_spec  pre post excep = 
    { pre=pre;
      post=post;
      excep=excep
    }

