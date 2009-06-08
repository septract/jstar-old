(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Pprinter
open Pterm
open Plogic 
open Rlogic
open Rterm
(** {1 Dotty} *)

type box_kind = Box of int * string * args list
		| Record of int * args * (args * args) list


let dangling_boxes= ref [] 
let dotty_state_count = ref 0
let current_state_id_box = ref 0
let dotty_state_id = ref 0
let curr_logic: Plogic.logic ref = ref Plogic.empty_logic
let curr_heap: Plogic.pform  ref = ref Plogic.mkFalse

(* list of all boxes in a state *)
let lbox: box_kind list ref = ref [] 

(* list of links between boxes *)
let edges_pairs = ref [] 


let exp_equal e e' = Prover.check_equal !curr_logic (Rlogic.convert !curr_heap) e e'

let reset_dotty_state_id () = dotty_state_id:=0


let rec look_up lb e = 
  match lb with
  | [] -> None 
  | Box(n,_,e'::_)::lb' 
  | Record(n,e',_)::lb' -> 
      if exp_equal e e' then 
	Some n  
      else look_up lb' e
  | _ -> assert false


let cut_name s = 
  let i=ref (String.length s -1) in
  while (s.[!i]<>' ') && (!i > 0) do 
    i:=!i-1
  done;
  if !i = 0 then s  else 
    (String.sub s 0 1) ^(String.sub s !i  (String.length s - !i-2 )) ^ (String.sub s 0 1)




let dotty_pp_state  f b =
  let rec make_label_fields i ld =
    match ld with 
    |[] -> ""
    |(fname,_)::ld' ->
       let sf=string_args fname in
       let sf =String.sub sf 2 (String.length sf - 4) in 
       " | <f"^(string_of_int i)^"> "^ sf ^(make_label_fields (i+1) ld')   
  in
  match b with 
  |Box(n,s,e::args) ->
     Printf.fprintf f "state%i [label=\"%s: %s \"]\n" n (string_args e) s
  | Record(n,e,ld) ->
      let s="<f0> "^(string_args e)^" "^make_label_fields 1 ld in
      Printf.fprintf f "state%i [shape=\"record\" label=\"%s\"]\n" n s
  | _ -> assert false


let dotty_pp_link f (n1,n2,lab)  =
  Printf.fprintf f "state%i -> state%i[label=%s];\n" n1 n2  (cut_name (string_args lab))

let add_box b = lbox:=b::!lbox

let update_box e d =
  let rec f lb = 
    match lb with 
    | [] -> []
    | Record(n,e',ld)::lb'-> 
	if exp_equal e e' then
	  Record(n,e',d::ld)::lb'
	else 
	  Record(n,e',ld)::f lb'
    | b::lb' -> b:: f lb'
  in
  lbox := f !lbox


let dotty_mk_box heap =
  let rec f exp_with_box sigma =
    let n = !dotty_state_count in
    let _ = incr dotty_state_count in
    match sigma with 
      [] -> []
    | SPred ("field",[e;nfield;e'])::sigma' ->
	if List.mem e exp_with_box then 
	  let _ = update_box e (nfield,e') in
	  f exp_with_box sigma'
	else 
	  let _=add_box (Record(n, e, [(nfield,e')]))  in
	  f (e::exp_with_box) sigma'
    | SPred (s,args)::sigma' ->
	add_box (Box(n,s,args));
	f exp_with_box sigma'
    | _ ->assert false
  in
  f [] (snd heap) 
   
let is_nil e =  (Logic.compare_arg e (Arg_op("null",[])) ) =0 || (Logic.compare_arg e (Arg_op("nil",[])) ) =0

let get_edge_pairs f b =
  let find_target_edge e =
    match look_up !lbox e with
    | None -> 
	let n' = !dotty_state_count in
 	let _ = incr dotty_state_count in
	let _ =if is_nil e then  
	  (* for the moment treating nil as special case of dangling box. 
	     dunno if it's a good idea *)
	  Printf.fprintf f "state%i [label=\"%s \", color=green, style=filled]\n" n'  (string_args e) 
	else 
	  Printf.fprintf f "state%i [label=\"%s \", color=red, style=filled]\n" n'  (string_args e) 
	in
	dangling_boxes:=(e,n')::!dangling_boxes;
	n'
    | Some n' -> n'
  in
  match b with 
  |Record(n,_,ld) -> 
     List.map (fun (lab,e) -> (n,find_target_edge e,lab)) ld
  |Box(n,s,e::ld) -> 
     (* assumption: the tird argument is a list of kind e::ld where
	e is the address of the cell and ld is the list of targets *)
     List.map (fun e' -> (n,find_target_edge e',Arg_string(""))) ld
  | _ -> assert false



(** Pretty print a form in dotty format. *)
let pp_dotty f heap lo =
  lbox:=[];
  dangling_boxes:=[]; 
  curr_heap:=heap;
  curr_logic:=lo;
  current_state_id_box:=!dotty_state_count;
  incr dotty_state_id;
  Printf.fprintf f "\n subgraph cluster_%i { \n" !dotty_state_count;
  Printf.fprintf f "\n state%i [label=\"PROP %i \",  style=filled, color= yellow]\n" !current_state_id_box !dotty_state_id;
  dotty_state_count:=!dotty_state_count+2;
  ignore(dotty_mk_box heap); 
  List.iter  (dotty_pp_state f)  !lbox;
  edges_pairs :=List.flatten( List.map (get_edge_pairs f) !lbox);
  List.iter (dotty_pp_link f) !edges_pairs;
  Printf.fprintf f "\n } \n" 



let print_formset_dotty fs dotty_file = 
  let outc = open_out dotty_file in
  let _=Dotty.reset_dotty_state_id () in
  let _ = Printf.fprintf outc "\n\n\ndigraph main { \nnode [shape=box];\n" in
  let _ = Printf.fprintf outc "\n compound = true; \n" in
  List.iter (fun f -> (Dotty.pp_dotty outc f !curr_logic) ) fs;
  Printf.fprintf outc  "\n}"; 
  close_out outc


(* print a dotty file for everynode in the cfg *)
let rec print_file_dotty dotty_file_base lnodes = 
    match lnodes with
    | [] -> ()
    | n::lnodes' -> 
	let id=node_get_id n in
	let fs=formset_table_find id in
	print_formset_dotty fs  (dotty_file_base^(string_of_int id)^".dot");
	print_file_dotty dotty_file_base lnodes'





