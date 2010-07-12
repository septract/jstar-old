(********************************************************
   This file is part of jStar 
	src/utils/config.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

(* In this file we can put all global flags *)

(** Flag for verbose mode *)
let verbose = ref false 

(** Flag for empty creating specs template *)
let specs_template_mode = ref false

(** Flag to print heaps on every node in the cfg *)
let dotty_print = ref false

let sym_debug = ref true

let symb_debug() = !sym_debug
  
let eclipse = ref false
  
let eclipse_mode() = !eclipse
