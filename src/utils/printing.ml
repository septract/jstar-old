(********************************************************
   This file is part of jStar 
	src/utils/printing.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
********************************************************)

module Source_pos_node_id_table = 
  Map.Make(struct 
	     type t = int 
	     let compare = compare
end)

type source_pos_tag = int * int * int * int
 
let source_pos_table : (source_pos_tag option) Source_pos_node_id_table.t ref = ref Source_pos_node_id_table.empty
  
let return_jimple_start_line node_id = 
  match Source_pos_node_id_table.find node_id !source_pos_table with
  | Some (x, _, _, _) -> x
  | None -> -1
    
let return_jimple_start_character node_id = 
  match Source_pos_node_id_table.find node_id !source_pos_table with
  | Some (_, _, x, _) -> x
  | None -> -1
    
let return_jimple_end_line node_id = 
  match Source_pos_node_id_table.find node_id !source_pos_table with
  | Some (_, x, _, _) -> x
  | None -> -1
    
let return_jimple_end_character node_id = 
  match Source_pos_node_id_table.find node_id !source_pos_table with
  | Some (_, _, _, x) -> x
  | None -> -1
    
let make_json_source_pos node_id text =
     Printf.printf "\njson {\"error_pos\": {\"sline\": \"%d\", \"eline\": \"%d\", \"spos\": \"%d\", \"epos\": \"%d\"}, \"error_text\": \"%s\"}\n"
     (return_jimple_start_line node_id) 
     (return_jimple_end_line node_id)
     (return_jimple_start_character node_id) 
     (return_jimple_end_character node_id)
     text
  
 (* let dump_table () =
   Printf.printf "\nPrint line table:\n\n";
   Source_pos_node_id_table.iter
   (fun sid pos ->
	   match pos with
	   | Some (sl, sp, el, ep) ->  Printf.printf "sid: %d   -->  (%d, %d, %d, %d)\n" sid sl sp el ep
	   | None -> Printf.printf "sid: %d   -->  None\n" sid
   )
    !source_pos_table*)
  
let printf node_id error_text =
  if Config.eclipse_mode() then
    match node_id with
  | Some id -> make_json_source_pos id error_text
  | None -> () 


