(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Pterm
open Plogic
open Pprinter
open Support_syntax

let class2args cl = Arg_string (class_name2str cl)

(* create n.si|->e *)
let mk_pointsto n si e = [P_SPred("field",[n; si; e])]

(* create cl1 <: cl2 *)
let mk_subtype cl1 cl2 = [P_PPred("subtype", (class2args cl1)::(class2args cl2)::[])]


let base_type2args ty = 
  Arg_string (Pprinter.j_base_type2str ty)

(* create var : cl   (precise type not static type) *) 
let objtype_name = "type"
let mk_type var cl = [P_PPred(objtype_name, var::(class2args cl)::[])]

let mk_type_all var cl = [P_PPred(objtype_name, var::(base_type2args cl)::[])]

let objtype receiver classname = [P_PPred(objtype_name, [(Arg_var receiver);(Arg_string classname)])]



(* create var <: cl  (is a subtype of) *)
let mk_objsubtyp var cl = P_PPred("objsubtype", var :: (class2args cl) :: [])

(* create var </: cl  (is not a subtype of) *)
let mk_objnotsubtyp var cl = P_PPred("notobjsubtype", var :: (class2args cl) :: [])
