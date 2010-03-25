(********************************************************
   This file is part of jStar 
	src/jimplefront/mkspecs.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Jparsetree
open Jimple_global_types

let  print_spec cname memb =
  match memb with
  |  Method (modl, jty,n, pars, tc, rc, ocs, ec, body) -> Printf.printf "\n%s\n" 
       ("static "^(Pprinter.signature2str (Method_signature (cname,jty,n,pars)))^" : { | } { | };")
  | _ -> ()


let rec print_specs_template program =
  match program with 
  | JFile ( _, _ , cname, _,_ ,ml) -> 
      Printf.printf "\n\n\nclass %s\n{" (Pprinter.class_name2str cname);  
      List.iter (print_spec cname) ml;
      Printf.printf "\n}\n\n\n"

