(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)

open Pterm
open Rterm
open Rlogic
open Plogic
open Jlogic
open Global_types
open Jparsetree
open Cfg
open Prover
open Specification
open Vars
open Support_symex

(* global variables *)
let curr_meth = ref ""
let curr_logic: Prover.logic ref = ref Prover.empty_logic
let curr_abs_rules: Prover.logic ref = ref Prover.empty_logic
let curr_static_methodSpecs:Specification.methodSpecs ref = ref Specification.emptyMSpecs
let curr_dynamic_methodSpecs:Specification.methodSpecs ref = ref Specification.emptyMSpecs



(* true if v is a primed variable *)
let is_primed (v: Vars.var) : bool = 
  match v with 
  | EVar _ -> true
  | _ -> false 


let this_var_name = Jlogic.this_var_name

let parameter n = "@parameter"^(string_of_int n)^":"

(* create the variable in the table for the object "this" *)
let mk_this_of_class () : Vars.var =
  let v=Vars.concretep_str this_var_name 
  in var_table_add (this_var_name) v;
  v

(* create entries in the variable table for a list of parameters *)
let mk_parameter_of_class (ps: Jparsetree.parameter list option) : unit =
  match ps with 
  | None -> ()
  | Some ps ->   
      for i=0 to List.length ps do
	let p=parameter i in 
	let v=Vars.concretep_str p
	in var_table_add p v
      done 


(* find the this-variable in the table *)
let get_this_of_class () =
  var_table_find (this_var_name)


(* define the constant name for the return variable. *)
(*let name_ret_var mname = (Pprinter.name2str mname)^"$"^"ret_var"*)
let name_ret_var = "$"^"ret_var"

(* create local program variables for methods. 
   mdl is the list of all methods in the class file.
   A special return variable (called method_name$ret) is created as well.
 *)
let create_program_variables mdl =
  let process_method md =
    let lv=snd (List.split md.locals) in
    let lv = List.map (fun v -> Var_name v) lv in
    let lv = Var_name(Identifier_name(name_ret_var))::lv in
    let locs= List.map (fun v -> variable2key v, Vars.concretep_str (variable2key v)) lv in
    List.iter (fun (k,v) -> var_table_add k v) locs
  in 
  List.iter process_method mdl


let make_field_signature  cname ty n =
  Field_signature(cname,ty,n) 


(* ================  transition system ==================  *)

type id = int



let fresh_node = let node_counter = ref 0 in fun () ->  let x = !node_counter in node_counter := x+1; x

let fresh_file = let file_id = ref 0 in fun () -> let x = !file_id in file_id := x+1;  Sys.getcwd() ^  "/proof_file_"^(string_of_int x)^".txt"

type ntype = 
    Plain | Good | Error | Abs | UnExplored

type node = {mutable content : string; id : id; mutable ntype : ntype; mutable url : string; mutable edges : edge list; cfg : Cfg.node option}
and  edge = string * string * node * node * string option

let graphe = ref []

module Idmap = 
  Map.Make(struct 
    type t = int option
    let compare = compare
  end)

let graphn = ref  Idmap.empty
let startnodes = ref []



let make_start_node node = startnodes := node::!startnodes

let escape_for_dot_label s =
  Str.global_replace (Str.regexp "\\\\n") "\\l" (String.escaped s)

let pp_dotty_transition_system () =
  let foname="execution.dot~" in
  let dotty_outf=open_out foname in
  if Config.symb_debug() then Printf.printf "\n Writing transition system file execution.dot  \n";
  Printf.fprintf dotty_outf "digraph main { \nnode [shape=box,  labeljust=l];\n\n";
  Idmap.iter 
    (fun cfg nodes ->
      ((match cfg with Some cfg -> Printf.fprintf dotty_outf "subgraph cluster_cfg%i {\n"  cfg | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=escape_for_dot_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	  Plain -> ()
	| Good ->  ()
	| Error ->  ()
	| UnExplored -> ()
	| Abs ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=yellow, style=filled%s]\n" id label url)
	nodes;
      match cfg with Some _ -> Printf.fprintf dotty_outf "\n}\n" | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=escape_for_dot_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with 
	  Plain ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l%s]\n" id label url
	| Good ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=green, style=filled%s]\n" id label url
	| Error ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=red, style=filled%s]\n" id label url
	| UnExplored ->  Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=orange, style=filled%s]\n" id label url
	| Abs -> () )
	nodes;
    )
    !graphn;
  List.iter (fun (l,c,s,d, o) ->
    let l = escape_for_dot_label l in
    let c = escape_for_dot_label c in
    Printf.fprintf dotty_outf "\n state%i -> state%i [label=\"%s\", tooltip\"%s\"%s]" s.id d.id l c
	    (match o with 
	      None -> ""
	    | Some f -> Printf.sprintf ", URL=\"file://%s\", fontcolor=blue" f))
    !graphe;
  Printf.fprintf dotty_outf "\n\n\n}";
  close_out dotty_outf;
  Sys.rename foname "execution.dot"




let add_node (label : string) (ty : ntype) (cfg : Cfg.node option) = 
  let id = fresh_node () in 
  let node = {content=label; id=id;ntype=ty;url=""; edges=[]; cfg = cfg} in 
  let cfgid = 
    match cfg with 
      None -> None 
    | Some cfg -> Some (node_get_id cfg) in 
  graphn := Idmap.add cfgid (node::(try Idmap.find cfgid !graphn with Not_found -> [])) !graphn;
  node

let add_error_node label = add_node label Error None
let add_abs_node label cfg = add_node label Abs (Some cfg)
let add_good_node label = add_node label Good None
let add_node_unexplored label cfg = add_node label UnExplored (Some cfg)
let add_node label cfg = add_node label UnExplored (Some cfg)


let explore_node src = if src.ntype = UnExplored then src.ntype <- Plain

let add_abs_heap_node (heap : Rlogic.ts_form) cfg= 
  (Format.fprintf (Format.str_formatter) "%a" (string_ts_form (Rterm.rao_create ())) heap);
  add_abs_node (Format.flush_str_formatter ()) cfg

let add_heap_node (heap : Rlogic.ts_form) cfg = 
  (Format.fprintf (Format.str_formatter) "%a" (string_ts_form (Rterm.rao_create ())) heap);
  add_node (Format.flush_str_formatter ()) cfg

let add_error_heap_node (heap : Rlogic.ts_form) = 
  (Format.fprintf (Format.str_formatter) "%a" (string_ts_form (Rterm.rao_create ())) heap);
  add_error_node (Format.flush_str_formatter ())


let x = ref 0

let add_edge src dest label = 
  let edge = (label, "", src, dest, None) in
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  explore_node src;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1

let add_edge_with_proof src dest label = 
  let f = fresh_file() in
  let out = open_out f in
  Prover.pprint_proof out;
  close_out out;
  explore_node src;
  let edge = (label, "", src, dest, Some f) in 
  graphe := edge::!graphe;
  src.edges <- edge::src.edges;
  if !x = 5 then (x:=0; pp_dotty_transition_system ()) else x :=!x+1


(*let add_edge_with_string_proof src dest label proof = 
  let f = fresh_file() in
  let out = open_out f in
  output_string out proof;
  close_out out;
  graphe := (label, src, dest, Some f)::!graphe*)

let add_url_to_node src proof = 
  let f = fresh_file() in
  let out = open_out f in
  output_string out proof;
  close_out out;
  src.url <- f


let add_id_form h cfg =
    let id=add_heap_node h cfg in
    (h,id)

let add_id_formset sheaps cfg =  List.map (fun h -> add_id_form h cfg) sheaps


let add_id_abs_form cfg h =
    let id=add_abs_heap_node h cfg in
    (h,id)

let add_id_abs_formset sheaps cfg =  List.map (add_id_abs_form cfg) sheaps





(* ================   ==================  *)


(* ================  work list algorithm ==================  *)

(* this type has support for  creating a transition system 
   (formula, id)
   id is a unique identifier of the formula
 *)
type formset_entry = Rlogic.ts_form * node

(* eventually this should be a more efficient data structure than list*)
type formset = formset_entry list 


type formset_hashtbl = (int, formset) Hashtbl.t

(* table associating a cfg node to a set of heaps *)
let formset_table : formset_hashtbl = Hashtbl.create 10000


let formset_table_add key s = 
  Hashtbl.add formset_table key s

let formset_table_replace key s = 
  Hashtbl.replace formset_table key s

let formset_table_mem key  = 
  Hashtbl.mem formset_table key 

let formset_table_find key =
  try 
    Hashtbl.find formset_table key
  with Not_found -> 
    warning(); let _ =Printf.printf "\n ERROR: cannot find formset for %i in the table. Abort! \n" key in
    reset(); assert false

let remove_id_formset formset =
  fst (List.split formset)

	      



(* execute  v=e *)
let exec_simple_assign (v:Jparsetree.variable) (e:Jparsetree.immediate) (sheap: Rlogic.ts_form) = 
  if Config.symb_debug() then Printf.printf "\nExecuting simple assignment statement\n ";
  let sheap = update_var_to (variable2var v) (immediate2args e) sheap in 
  [sheap]


(* execute  v=bop x y : TODO THIS *)
let exec_binop_assign (v:Jparsetree.variable) (e: Jparsetree.expression) (sheap: Rlogic.ts_form) = 
  if Config.symb_debug() then Printf.printf "\nExecuting binop assignment statement\n ";
  let sheap = update_var_to (variable2var v) (expression2args e) sheap in
  [sheap]


(* execute  "r0 := @this: LinkedList" *)
let exec_identity_stmt  n id ty (sheap: Rlogic.ts_form) = 
  if Config.symb_debug() then Printf.printf "\nExecuting identity statement\n ";
  let sheap = update_var_to (variable2var (Var_name n)) (identifier2args id) sheap in 
  sheap

(* execute v=[e] *)
let exec_lookup_assign (v:Jparsetree.variable) (e:Jparsetree.reference) (sheap,id) node = 
  if Config.symb_debug() then Printf.printf "\nExecuting lookup statement\n ";
  let e_var = freshe() in
  let pointed_to_var = Arg_var (e_var) in
  let find_pointsto = 
    match e with 
    | Field_local_ref (n,si) -> 
	mk_pointsto (name2args n) (signature2args si) pointed_to_var
    | _ -> assert false  (* TODO other types of reference *) in   
  let frames = check_implication_frame_pform (!curr_logic) sheap find_pointsto in
  match frames with 
    [] ->      
      let idd = add_error_node "ERROR" in 
      add_edge_with_proof id idd 
	(Format.fprintf (Format.str_formatter) "%s:@\n %a" (Pprinter.statement2str (node_get_stmt node).skind) Prover.pprint_counter_example (); Format.flush_str_formatter ());
      warning(); 
      Printf.printf "\n\nERROR: While executing node %d:\n   %s\n"  (node_get_id node) (Pprinter.statement2str (node_get_stmt node).skind);
      Prover.print_counter_example ();
      Printf.printf "\nCannot find location!\n"; 
      reset(); []
  | _-> ();
  List.map
    (fun res -> 
      (* put back the points to *)
      let res = conj_convert find_pointsto res  in 
      (* perform assignment *)
      let res = update_var_to (variable2var v) pointed_to_var res in 
      kill_var e_var res; res
    )
    frames


(* execute  [v]=e *)
let exec_mutation_assign  (v:Jparsetree.reference) (e:Jparsetree.immediate) (sheap,id)  node = 
  let e_var = freshe() in
  let pointed_to_var = Arg_var (e_var) in
  let find_pointsto,new_pointsto = 
    match v with 
    | Field_local_ref (n,si) -> 
	mk_pointsto (name2args n) (signature2args si) pointed_to_var,
	mk_pointsto (name2args n) (signature2args si) (immediate2args e) 
    | _ -> assert false  (* TODO other types of reference *) in    
  let frames = check_implication_frame_pform (!curr_logic) sheap find_pointsto in
  match frames with 
    [] ->
      let idd = add_error_node "Error" in 
      add_edge_with_proof id idd
	(Format.fprintf (Format.str_formatter) "%s:@\n %a" (Pprinter.statement2str (node_get_stmt node).skind) Prover.pprint_counter_example (); Format.flush_str_formatter ());
      warning(); 
      Printf.printf "\n\nERROR: While executing node %d:\n   %s\n"  
	(node_get_id node) 
	(Pprinter.statement2str (node_get_stmt node).skind);
      Prover.print_counter_example ();
      Printf.printf "\nCannot find location!\n"; 
      reset();
      [](*assert false *)
  | _-> ();
  List.map
    (fun res -> 
      (* put back the new points to *)
      if Config.symb_debug() then Format.printf "@\nBefore update@\n   %a@\n" (string_ts_form (Rterm.rao_create ())) res;
      let x = conj_convert new_pointsto res in
      kill_var e_var res;
      if Config.symb_debug() then Format.printf "@\nAfter update@\n   %a@\n" (string_ts_form (Rterm.rao_create ())) x;
      x
    )
    frames

(* execute x=new(ty).     
   We treat it as just substituting a fresh existentially quantified
   variable in place of x.  Also we pick up a new primed variable for
   the value of x. This is because we could create wrong aliases with
   the primed variable given in the specs (since they get a fixed name
   EVar (_this1,0), (_this2,0), (_this3,0)....).  The rest of the job
   will be performed by the invocation to specialinvoke <init>
*)
let exec_simple_allocation  x ty sheap = 
  kill_var (variable2var x) sheap;
  [conj_convert (Jlogic.mk_type_all (var2args (variable2var x)) ty) sheap ]


(* retrieve dynamic spec of a method from table of specs*)
let get_dynamic_spec si = 
  match si with 
  | Method_signature ms ->
      (try 
	 Some (MethodMap.find ms !curr_dynamic_methodSpecs  )
       with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false


(* retrieve static spec of a method from table of specs*)
let get_static_spec si = 
  match si with 
  | Method_signature ms ->
      (try 
	Some (MethodMap.find ms !curr_static_methodSpecs  )
      with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false



let get_class_name_from_signature si =
  match si with
  | Method_signature (c,_,_,_) -> c
  | Field_signature (c,_,_) ->c


let signature_get_name si =
  match si with 
  | Method_signature (_,_,n,_) -> n
  | Field_signature (_,_,n) -> n


let invoke_exp_get_signature ie =
  match ie with 
  | Invoke_nostatic_exp(_, _, si, _) -> si
  | Invoke_static_exp(si,_) -> si


let rec param_sub il num sub = 
  match il with 
    [] -> sub
  | i::il -> param_sub il (num+1) (add (Vars.concretep_str (parameter num)) (immediate2args i) sub)



let param_sub il =
  let ret_var = concretep_str name_ret_var in 
  let sub' = add ret_var (Arg_var(var_table_find (name_ret_var)))  empty in 
  match il with Some il -> param_sub il 0 sub' | None -> sub'
  


let param_this_sub il n = 
  let sub = param_sub il in 
  let nthis_var = concretep_str this_var_name in 
  add nthis_var (name2args n)  sub 
 

let call_jsr_static (sheap,id) spec il si node = 
  let sub' = param_sub il in
  let sub''= freshening_subs sub' in
  let spec'=Specification.sub_spec sub'' spec  in 
  let res = (jsr !curr_logic sheap spec') in
    match res with 
      None -> Printf.printf "\n\n I cannot find splitting to apply spec. Giving up! \n\n"; assert false
    | Some r -> fst r


let call_jsr (sheap,id) spec n il si node = 
  let sub' = param_this_sub il n in 
  let sub''= freshening_subs sub' in
  let spec'=Specification.sub_spec sub'' spec  in 
  let res = (jsr !curr_logic sheap spec') in
    match res with 
      None ->   
	let idd = add_error_node "ERROR" in
	add_edge_with_proof id idd 	
	  (Format.fprintf 
	     (Format.str_formatter) "%s:@\n %a" 
	     (Pprinter.statement2str (node_get_stmt node).skind) 
	     Prover.pprint_counter_example (); 
	   Format.flush_str_formatter ());
        warning();
	Printf.printf "\n\nERROR: While executing node %d:\n   %s\n"  (node_get_id node) (Pprinter.statement2str (node_get_stmt node).skind);
	Prover.print_counter_example ();
	reset(); 
	[]
	(*assert false*)
(*	  "Preheap:\n    %s\n\nPrecondition:\n   %s\nCannot find splitting to apply spec. Giving up! \n\n" sheap_string (Plogic.string_form spec.pre); assert false *)
    | Some r -> fst r


  
(* execute method calls *)
let exec_invoke_stmt  (iexp: Jparsetree.invoke_expr) sheap  node = 
  if Config.symb_debug() then Printf.printf "\nExecuting invoke statement\n ";
  match iexp with
  | Invoke_nostatic_exp (Virtual_invoke,n,si,il) 
  | Invoke_nostatic_exp (Interface_invoke,n,si,il) ->  (* ddino: we deal with interface invoke as for virtual invoke. Not sure it's correct!!!*)
      (match get_dynamic_spec si with
       | Some dspec -> call_jsr  sheap dspec n il si node
       | _ -> 
	   warning(); Printf.printf "\n No dynamic specs found for %s. Abort!\n\n" (Pprinter.signature2str si); reset();
	   assert false	  
      )
  | Invoke_nostatic_exp (Special_invoke,n,si,il) ->
      (match get_static_spec si with
      | Some sspec -> call_jsr  sheap sspec n il si node
      |  _ ->	
	   warning(); Printf.printf "\n No static specs found for %s. Abort!\n\n" (Pprinter.signature2str si); reset();
	   assert false	  
      )
  | Invoke_static_exp (si,il) -> 
      (match get_static_spec si with
      | Some sspec -> call_jsr_static  sheap sspec il si node
      |  _ ->	
	   warning(); Printf.printf "\n No static specs found for %s. Abort!\n\n" (Pprinter.signature2str si); reset();
	   assert false	  
      )



let exec_method_invocation  (v:Jparsetree.variable) (ie: Jparsetree.invoke_expr) sheap  n =
(*  let mname =signature_get_name (invoke_exp_get_signature ie) in*)
  let ret_var = var_table_find (name_ret_var) in
  let v_var=variable2var v in
  let eliminate_ret_var h =
    let h = update_var_to v_var (Arg_var ret_var) h in 
    kill_var ret_var h;
    h
(*    let v'=Arg_var (Vars.freshe_str (Pprinter.variable2str v)) in
    let sub=add v_var v' empty in
    let h'=subst_form sub h in
    let sub'= add ret_var (Arg_var v_var) empty in
    subst_form sub' h'  *)
  in
  let heaps'=exec_invoke_stmt  ie sheap n in
  List.map eliminate_ret_var heaps'

(* true if e is a variable starting with $ sign. They are special variable 
in jimple and need to e treated in special way  *)
let is_dollar_variable e =
  match e with 
    Immediate_local_name (Identifier_name x) -> 
      (String.sub x 0 1) = "$" 
  | _ -> false


let immediate2var e = 
  match immediate2args e with 
    Arg_var v -> v
  | _ -> assert false


let exec_assign_stmt  (v:Jparsetree.variable) (e:Jparsetree.expression) (sheap,id)  node : Rlogic.ts_form list =
  match v, e with 
  | Var_ref r, Immediate_exp e'  -> 
      let hs=exec_mutation_assign  r e' (sheap,id) node in
      (* if e is a dollar variable and we have used then it's not
	 gonna be used anymore.  We need to get rid of it because
	 otherwise we diverge.  We existentially quantify it and
	 abstraction will remove it.  
	 The check is probably unnecessary. But just to be sure.
      *)
(*      if is_dollar_variable e' then 
	List.iter (fun h -> kill_var (immediate2var e') h) hs;*)
      hs
  | Var_name n, Immediate_exp e' -> 
      let hs=exec_simple_assign   v e' sheap in
      (* as commented above *)
(*      if is_dollar_variable e' then 
	List.iter (fun h -> kill_var (immediate2var e') h) hs;*)
      hs
  | Var_name n, Reference_exp r  -> exec_lookup_assign  v r (sheap,id) node
  | Var_name n, New_simple_exp ty -> exec_simple_allocation  v ty sheap
  | Var_name n , Invoke_exp ie ->  exec_method_invocation  v ie (sheap,id) node
  | Var_name n , Binop_exp(name,x,y)-> exec_binop_assign v (Binop_exp(name,x,y)) sheap
  | Var_name n , Cast_exp (_,e') -> (* TODO : needs something for the cast *) 
      exec_simple_assign  v e' sheap
  | _ , _ -> assert false 


let exec_goto_stmt (sheap: Rlogic.ts_form) = [sheap]

let exec_nop_stmt (sheap: Rlogic.ts_form) = [sheap]

let exec_label_stmt (sheap: Rlogic.ts_form) = [sheap]


(* for return v adds the equality ret=v otherwise it behaves as skip *)
let exec_return_stmt stm v (sheap: Rlogic.ts_form) = 
  match v with 
   | Some imm -> 
       let rvar = Var_name(Identifier_name(name_ret_var)) in
       let sheap = update_var_to (variable2var rvar) (immediate2args imm) sheap in 
       sheap
   | None -> sheap


(* this just pass forward sheap. The expression to the successor of the 
true branch and the negation of the expression to the successor of the false branch 
are added by the function  add_if_expressions below.
*)
let exec_if_stmt (sheap: Rlogic.ts_form) = [sheap]


let exec_breakpoint_stmt (sheap: Rlogic.ts_form) = assert false


let exec_entermonitor_stmt (sheap: Rlogic.ts_form) = assert false


let exec_exitmonitor_stmt (sheap: Rlogic.ts_form) = assert false


let exec_tableswitch_stmt (sheap: Rlogic.ts_form) = assert false


let exec_lookupwitch_stmt (sheap: Rlogic.ts_form) = assert false


let exec_identity_no_type_stmt (sheap: Rlogic.ts_form) = assert false


let exec_throw_stmt (sheap: Rlogic.ts_form) = assert false

(* checks if x \in fset. membership is considered up to logical equivalence *)
let rec formset_mem lo x fset =
  match fset with 
  | [] -> false
  | y::fset' -> 
      ((check_implication lo x y) && (check_implication lo y x)) || (formset_mem lo x fset') 

let compact_formset lo xs = 
  let rec impl xs ys = 
    match ys with 
      [] -> xs
    | y::ys -> 
	let xs = List.filter 
	    (fun x -> 
	      if (Prover.check_implication lo x y) then false else true) xs in 
	let ys = List.filter 
	    (fun x -> 
	      if (Prover.check_implication lo x y) then false else true) ys in 
	impl (y::xs) ys
  in (*Debug.debug_ref:=true; *)let xs = impl [] xs in (*Debug.debug_ref:=false;*) xs

(** implements s1 U s2  *)
let rec union_formsets lo s2 s1 =
(*  compact_formset lo (s2@s1)*)
  match s1 with 
  | [] -> s2
  | s::s1' -> 
      if (formset_mem lo s s2) then 
	union_formsets lo s2 s1'  
      else s::(union_formsets lo s2 s1') 

let worklist = ref []

let add_worklist n = 
  worklist := n::!worklist

exception Contained

let rec execute_stmt n (sheap : formset_entry) : unit =
  let sheap_noid=fst sheap in
  Rlogic.kill_all_exists_names sheap_noid;
  let stm=node_get_stmt n in
  if Config.symb_debug() then Format.printf "@\nExecuting statement:@ %s" (Pprinter.statement2str stm.skind); 
  if Config.symb_debug() then Format.printf "@\nwith heap:@\n    %a@\n@\n@."  (string_ts_form (Rterm.rao_create ())) sheap_noid;
  if (Prover.check_inconsistency !curr_logic (form_clone sheap_noid false)) then 
    (if Config.symb_debug() then Printf.printf "\n\nInconsistent heap. Skip it!\n";
     let idd = add_good_node "Inconsistent"  in add_edge_with_proof (snd sheap) idd "proof";
     ())
  else (
  if Config.symb_debug() then Printf.printf "\nStarting execution of node %i \n" (node_get_id n);
  match n.nd_kind with 
  | Exit_node -> 
      if Config.symb_debug() then Printf.printf "Exit node %i\n" (node_get_id n);
    (* Check implies post-condtion *)
      let m = match n.nd_method with Some x -> x.pd_md | _ -> assert false in 
      let heaps= formset_table_find (node_get_id n) in
      (
       try 
	let heap,id = List.find (fun (heap,id) -> (check_implication_frame !curr_logic sheap_noid heap)!=[]) heaps in
	if Config.symb_debug() then Printf.printf "\n\nPost okay %s \n" (Pprinter.name2str m.name);

(*	let idd = add_good_node ("EXIT: "^(Pprinter.name2str m.name)) in *)
	add_edge_with_proof (snd sheap) id "exit";
(*	add_edge id idd "";*)
       with Not_found -> 
	 warning();
	 let _= Printf.printf "\n\nERROR: cannot prove post for method %s\n" (Pprinter.name2str m.name) in
	Prover.print_counter_example ();
	 reset();
	List.iter (fun heap -> 
	  let idd = add_error_heap_node (fst heap) in 
	  add_edge_with_proof (snd sheap) idd 
	  (Format.fprintf 
	     (Format.str_formatter) "ERROR EXIT: %s:@\n %a" 
	     (Pprinter.name2str m.name) 
	     Prover.pprint_counter_example (); 
	   Format.flush_str_formatter ()))
	   heaps
	(*print_formset "\n\n Failed Heap:\n" [sheap]    *)
      )
  | _ -> 
  let exec n sheap = 
    let sheap_noid=fst sheap in
    Rlogic.kill_all_exists_names sheap_noid;
    if Config.symb_debug() then Format.printf "Output to %i with heap@\n   %a@\n" (node_get_id n) (string_ts_form (Rterm.rao_create ())) sheap_noid;
    execute_stmt n sheap in 
  let execs n sheaps = List.iter (exec n) sheaps in 
(*  let minfo=node_get_method_cfg_info n in *)
  let succs=node_get_succs n in
  let id_clone h = (form_clone (fst h) false, snd h) in 
  let execs_one sheaps = 
    match succs with 
      [s] -> execs s sheaps 
    | _ -> assert false in
  let exec_one sheaps = 
    match succs with 
      [s] -> exec s sheaps 
    | _ -> assert false in
  if Config.symb_debug() then Format.printf "@\nExecuting statement:@ %s%!" (Pprinter.statement2str stm.skind); 
  if Config.symb_debug() then Format.printf "@\nwith heap:@\n    %a@\n@\n%!"  (string_ts_form (Rterm.rao_create ())) sheap_noid;
    (match stm.skind with 
      | Label_stmt l -> 
	  (*  Update the labels formset, if sheap already implied then fine, otherwise or it in. *)
	  (let id = node_get_id n in 
	  try
	    if Config.symb_debug() then Format.printf "@\nPre-abstraction:@\n    %a@."  (string_ts_form (Rterm.rao_create ())) sheap_noid;
	    let sheap_pre_abs = form_clone sheap_noid true in 
	    let sheaps_abs = Prover.abs !curr_abs_rules sheap_pre_abs in 
	    if Config.symb_debug() then Format.printf "@\nPost-abstractionc count:@\n    %d@."  (List.length sheaps_abs);
	    List.iter Rlogic.kill_all_exists_names sheaps_abs;
	    if Config.symb_debug() then List.iter (fun sheap -> Format.printf "@\nPost-abstraction:@\n    %a@."  (string_ts_form (Rterm.rao_create ())) sheap) sheaps_abs;

	    let formset = (formset_table_find id) in 
	    if Config.symb_debug() then (
               Format.printf "Testing inclusion of :@    %a" 
		  (Debug.list_format "@\n" (string_ts_form (Rterm.rao_create ()))) sheaps_abs;
               print_formset "in " (remove_id_formset formset)
	     );
	    explore_node (snd sheap);
	    let sheaps_with_id = add_id_abs_formset sheaps_abs n in
	    List.iter (fun sheap2 ->  add_edge_with_proof (snd sheap) (snd sheap2) ("Abstract@"^Pprinter.statement2str stm.skind)) sheaps_with_id;
	    let sheaps_with_id = List.filter 
		(fun (sheap2,id2) -> 
		  (let s = ref "" in 
		  if  
		    (List.for_all
		       (fun (form,id) -> 
			 if check_implication !curr_logic (form_clone sheap2 false) form  then 
			    (add_edge_with_proof id2 id ("Contains@"^Pprinter.statement2str stm.skind) ;false) 
			 else true)
		       formset)
		  then ( 
		    if String.length !s != 0 then (add_url_to_node id2 !s); true
		   ) else false
		  )
		)
		sheaps_with_id in
(*	    List.iter (fun h ->
			 add_edge (snd sheap) (snd h) (Pprinter.statement2str stm.skind)) sheaps_with_id;*)
	    formset_table_replace id (sheaps_with_id @ formset);
	    execs_one (List.map id_clone sheaps_with_id)
	  with Contained -> if Config.symb_debug() then Printf.printf "Formula contained.\n")
      | Identity_stmt (nn,id,ty) -> 
	  let h=exec_identity_stmt  nn id ty (fst sheap) in
	  let h=add_id_form h n in
	  add_edge (snd sheap) (snd h) (Pprinter.statement2str stm.skind);
	  exec_one h 
      | Identity_no_type_stmt(n,id) -> assert false (*exec_identity_no_type_stmt sheap*)
      | Assign_stmt(v,e) -> 
	  let hs=(exec_assign_stmt  v e sheap n) in
	  let hs=add_id_formset hs n in
	  List.iter (fun h ->
	    match e with 
	    | New_simple_exp _
	    | Immediate_exp _
	    | Binop_exp (_,_,_)
	    | Unop_exp (_,_)
	    | New_array_exp (_,_)
	    | New_multiarray_exp (_,_)
	    | Cast_exp (_,_)
	    | Instanceof_exp (_,_)
	      -> add_edge (snd sheap) (snd h) (Pprinter.statement2str stm.skind)
	    | Invoke_exp _
	    | Reference_exp _
	      -> add_edge_with_proof (snd sheap) (snd h) (Pprinter.statement2str stm.skind)
		    
		    ) hs;
	  execs_one hs
      | If_stmt(e,l) ->
	  let sheap2 = (form_clone (fst sheap) false, snd sheap) in 
	  (match succs with
	  | [s1;s2] ->  
	      (match s1.nd_stmt.skind with
	      | Label_stmt l' when l'=l -> 
		  let cc_h=(conj_convert (expression2pure e) (fst sheap)) in
		  let cc_h_id = add_id_form cc_h n in 
		  add_edge (snd sheap) (snd cc_h_id) (Pprinter.expression2str e);
		  let cc_h2=(conj_convert (expression2pure (negate e)) (fst sheap2)) in
		  let cc_h2_id = add_id_form cc_h2 n in 
		  add_edge (snd sheap) (snd cc_h2_id) (Pprinter.expression2str (negate e));
		  exec s1 cc_h_id;
		  exec s2 (cc_h2_id)
	      | _ -> 
		  let cc_h=(conj_convert (expression2pure (negate e)) (fst sheap)) in
		  let cc_h_id = add_id_form cc_h n in 
		  add_edge (snd sheap) (snd cc_h_id) (Pprinter.expression2str (negate e));
		  let cc_h2=(conj_convert (expression2pure e) (fst sheap2)) in
		  let cc_h2_id = add_id_form cc_h2 n in 
		  add_edge (snd sheap) (snd cc_h2_id) (Pprinter.expression2str e);
		  exec s1 cc_h_id;
		  exec s2 (cc_h2_id)
	      )
	  | _ -> assert false )
      | Goto_stmt _ | Nop_stmt  -> exec_one sheap
      | Ret_stmt v (* I treat this like return *) 
      | Return_stmt v -> 
	  let h=exec_return_stmt stm v (fst sheap) in
	  let h=add_id_form h n in
	  add_edge (snd sheap) (snd h) (Pprinter.statement2str stm.skind);
	  exec_one h
      | Invoke_stmt ie -> 
	  let hs=(exec_invoke_stmt ie sheap n) in
	  let hs=add_id_formset hs n in
	  List.iter (fun h -> 
		       add_edge_with_proof (snd sheap) (snd h) (Pprinter.statement2str stm.skind) ) hs;
	  execs_one hs
      (* TODO These ones *)
      | Throw_stmt _ | Breakpoint_stmt | Entermonitor_stmt _ | Exitmonitor_stmt _ 
      | Tableswitch_stmt (_,_) | Lookupswitch_stmt (_,_) -> assert false 

    ))
(*    if symb_debug() then print_formset "concrete results with heap:"  sheap_list;
    let abs_heaps= List.fold_left (union_formsets (!curr_logic)) [] (List.map (Abs.apply_abstraction !curr_abs_rules) sheap_list)  in
    if symb_debug() then print_formset "After abstraction:"  abs_heaps;
    abs_heaps)*)



(* 
recognise if md describes a init method. At the moment it only uses the name. But
maybe we should use a stronger condition
*)
let is_init_method md = Pprinter.name2str md.name ="<init>"


(* set initial formset of cfg nodes to start the fixed point
   computation.  This formset is the precondition defined in the spec file
*)
let initialize_node_formsets mdl fields cname= 
  let this =mk_this_of_class () in
  let rec make_this_fields fl=
    match fl with
    |[] -> []
    | Field(mol,ty,n)::fl' -> 
	let e = Support_symex.default_for ty n in 
	let si=make_field_signature cname ty n in
	pconjunction (mk_pointsto (var2args this) (signature2args si) e) (make_this_fields fl')
    | _ -> assert false
  in
  let class_this_fields=make_this_fields fields in
  let initialize_method_starting_node m = (* initialize starting node of m with spec *)
    let msi = Methdec.get_msig m cname in
    let _=mk_parameter_of_class m.params in
    let spec=
      try 
	MethodMap.find msi !curr_static_methodSpecs 
      with  Not_found -> 
	warning(); Format.printf "\n\n Error: Cannot find spec for method %s %s\n\n" (Pprinter.name2str m.name) (Pprinter.class_name2str m.class_name); reset();
	assert false
    in
    let meth_initial_form=if is_init_method m then (* we treat <init> in a special way*)
      pconjunction spec.pre class_this_fields 
    else spec.pre 
    in 
    let minfo=Cfg.mcfginfo_tbl_find (key_method m) in
    let start_node=method_cfg_info_get_start_node minfo in
    let end_node=method_cfg_info_get_exit_node minfo in
    let meth_initial_form_noid = convert meth_initial_form in
    let meth_initial_form = add_id_form meth_initial_form_noid start_node in 
    let id = add_good_node ("METHOD: "^(Pprinter.name2str m.name)) in 
    make_start_node id;
    let id_exit = add_good_node ("EXIT: "^(Pprinter.name2str m.name)) in 
    add_edge id (snd meth_initial_form) "";
    let meth_initial_formset =  [meth_initial_form] in
    let meth_final_formset_noid = [convert spec.post] in 
    let meth_final_formset = add_id_formset meth_final_formset_noid end_node in
    List.iter (fun (_,id) -> add_edge id id_exit "") meth_final_formset; 
    if Config.symb_debug () then print_formset ("\n"^(Pprinter.name2str m.name)^" init_form=") [meth_initial_form_noid] ;
    if Config.symb_debug () then print_formset ("\n"^(Pprinter.name2str m.name)^" final_form=") meth_final_formset_noid ;
    formset_table_replace (node_get_id start_node) meth_initial_formset;
    formset_table_replace (node_get_id end_node) meth_final_formset;
  in
  List.iter (fun n -> formset_table_add (node_get_id n) []) (Cfg.get_all_nodes ());
  List.iter initialize_method_starting_node mdl


let nodes_meth2list md =
  let rec collect tovisit collected =
    match tovisit with
    | [] -> collected 
    | n::tovisit' -> 
	if List.mem n collected  then 
	  collect tovisit' collected
	else collect ((node_get_succs n) @ tovisit') (n::collected) 
  in
  let minfo=Cfg.mcfginfo_tbl_find (key_method md) in
  let sn=method_cfg_info_get_start_node minfo in
  collect [sn] []


let rec icfg_nodes2list mdl = 
  match mdl with
  |[] -> []
  | md::mdl' ->
      (List.rev (nodes_meth2list md)) @ icfg_nodes2list mdl' 


let print_list_of_nodes s l=  
  if Config.symb_debug() then Format.printf "\n\n %s = [" s;
  List.iter (fun n -> if Config.symb_debug() then Format.printf " %i " (node_get_id n) ) l;
  if Config.symb_debug() then Format.printf " ]\n\n"











(* implements a work-list fidex point algorithm *)
(* the queue qu is a list of pairs [(node, expression option)...] the expression
is used to deal with if statement. It is the expression of the if statement is the predecessor
of the node is a if_stmt otherwise is None. In the beginning is always None for each node *)
let compute_fixed_point (f : Jparsetree.jimple_file) 
(apfmap : logic Global_types.ClassMap.t) (lo : logic) (abs_rules : logic)
(sspecs: Specification.methodSpecs) (dspecs: Specification.methodSpecs)  =
(*  HACK HACK HACK:  
   This is so that the exist vars are dealt with correctly between verification of body, and use for calls. *)
  let sspecs_prog = MethodMap.map (logical_vars_to_prog) sspecs in 
  curr_static_methodSpecs:= sspecs_prog;
(* end of HACK *)
  curr_dynamic_methodSpecs:=dspecs;
  let cname=Methdec.get_class_name f in
  let mdl =  Methdec.make_methdecs_of_list cname (Methdec.get_list_methods f) in
(* remove methods that are declared abstraction *)
  let mdl = List.filter (fun y -> List.for_all (fun x-> Abstract<>x) (y.modifiers)) mdl in  
  let fields=Methdec.get_list_fields f in
  let lo = try let x=Global_types.ClassMap.find cname apfmap in x with Not_found -> lo in
  curr_logic:= lo;
  curr_abs_rules:=abs_rules;
  compute_icfg mdl;
  create_program_variables mdl; 
  initialize_node_formsets mdl fields cname;  
(*  HACK HACK HACK:  
   This is so that the exist vars are dealt with correctly between verification of body, and use for calls. *)
  curr_static_methodSpecs:=sspecs;
(* HACK over *)
  worklist := List.filter (fun n -> (if Config.symb_debug() then print_node n); match n.nd_kind with Start_node -> (if Config.symb_debug() then Printf.printf "Start node %i\n" (node_get_id n));true | _ -> false) (icfg_nodes2list mdl);
  while (!worklist<>[]) do 
    let v=List.hd !worklist in
    worklist := List.tl !worklist;
    List.iter (fun f -> execute_stmt v f) (formset_table_find (node_get_id v));
    if Config.symb_debug() then Printf.printf "\nEnd execution of node %i \n" (node_get_id v)
  done 
(*  if !Config.dotty_print then print_file_dotty "conf_node" (icfg_nodes2list mdl);*)
(*  List.iter (fun m -> check_post sspecs_prog m lo cname) mdl*)
