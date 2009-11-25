open Jparsetree
open Vars
(*open Rterm *)
open Pterm
open Plogic 
open Rterm
open Rlogic
open Prover
open Specification



type methodspec =
      Dynamic of method_signature_short * (spec list)
  |   Static of method_signature_short * (spec list)

type methodspecs =
    methodspec list

type apf_define = (string * var * fldlist * Plogic.pform * bool)

type apf_defines = apf_define list

type class_spec = (class_name * apf_defines * methodspecs)





