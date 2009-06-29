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


(* ================  work list algorithm ==================  *)

(* this type has support for  creating a transition system 
   (formula, id)
   id is a unique identifier of the formula
 *)
type formset_entry = Rlogic.ts_form * int 

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

	      

(* ================  transition system ==================  *)

type transition = formset_entry * string * formset_entry

let transition_system = ref [] 

let add_transition_TS (t : formset_entry * string * formset_entry) = transition_system:=t::!transition_system 

let get_transition_system () = !transition_system

let counter_TS = ref 0

let get_counter_TS () = !counter_TS

let inc_counter_TS () = 
  counter_TS:=!counter_TS +1


let add_id_form h =
    let id=get_counter_TS () in
    inc_counter_TS ();
    (h,id)

let add_id_formset sheaps =  List.map add_id_form sheaps



(* ================   ==================  *)


(* execute  v=e *)
let exec_simple_assign (v:Jparsetree.variable) (e:Jparsetree.immediate) (sheap: Rlogic.ts_form) = 
  if symb_debug() then Printf.printf "\nExecuting simple assignment statement\n ";
  let sheap = update_var_to (variable2var v) (immediate2args e) sheap in 
  [sheap]


(* execute  v=bop x y : TODO THIS *)
let exec_binop_assign (v:Jparsetree.variable) (e: Jparsetree.expression) (sheap: Rlogic.ts_form) = 
  if symb_debug() then Printf.printf "\nExecuting binop assignment statement\n ";
  let sheap = update_var_to (variable2var v) (expression2args e) sheap in
  [sheap]


(* execute  "r0 := @this: LinkedList" *)
let exec_identity_stmt  n id ty (sheap: Rlogic.ts_form) = 
  if symb_debug() then Printf.printf "\nExecuting identity statement\n ";
  let sheap = update_var_to (variable2var (Var_name n)) (identifier2args id) sheap in 
  sheap

(* execute v=[e] *)
let exec_lookup_assign (v:Jparsetree.variable) (e:Jparsetree.reference) (sheap,id) node = 
  if symb_debug() then Printf.printf "\nExecuting lookup statement\n ";
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
      add_transition_TS ((sheap,id),"ERROR: "^(Pprinter.statement2str (node_get_stmt node).skind),(sheap,id)); 
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
      add_transition_TS ((sheap,id),"ERROR: "^(Pprinter.statement2str (node_get_stmt node).skind),(sheap,id));
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
      if symb_debug() then Format.printf "@\nBefore update@\n   %a@\n" (string_ts_form (Rterm.rao_create ())) res;
      let x = conj_convert new_pointsto res in
      kill_var e_var res;
      if symb_debug() then Format.printf "@\nAfter update@\n   %a@\n" (string_ts_form (Rterm.rao_create ())) x;
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
  [sheap]


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
	add_transition_TS ((sheap,id),"ERROR: "^ (Pprinter.statement2str (node_get_stmt node).skind),(sheap,id));
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
  if symb_debug() then Printf.printf "\nExecuting invoke statement\n ";
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
  if symb_debug() then Format.printf "@\nExecuting statement:@ %s" (Pprinter.statement2str stm.skind); 
  if symb_debug() then Format.printf "@\nwith heap:@\n    %a@\n@\n@."  (string_ts_form (Rterm.rao_create ())) sheap_noid;
  if (Prover.check_inconsistency !curr_logic (form_clone sheap_noid)) then 
    (if symb_debug() then Printf.printf "\n\nInconsistent heap. Skip it!\n";
     ())
  else (
  if symb_debug() then Printf.printf "\nStarting execution of node %i \n" (node_get_id n);
  match n.nd_kind with 
  | Exit_node -> 
      if symb_debug() then Printf.printf "Exit node %i\n" (node_get_id n);
    (* Check implies post-condtion *)
      let m = match n.nd_method with Some x -> x.pd_md | _ -> assert false in 
      let heaps= formset_table_find (node_get_id n) in
      (
       try 
	let heap,id = List.find (fun (heap,id) -> (check_implication_frame !curr_logic sheap_noid heap)!=[]) heaps in
	if !Support_symex.sym_debug then Printf.printf "\n\nPost okay %s \n" (Pprinter.name2str m.name);
	add_transition_TS (sheap,"EXIT: "^(Pprinter.name2str m.name), (heap,id));
       with Not_found -> 
	 warning();
	 let _= Printf.printf "\n\nERROR: cannot prove post for method %s\n" (Pprinter.name2str m.name) in
	Prover.print_counter_example ();
	 reset();
	List.iter (fun heap -> add_transition_TS (sheap,"ERROR EXIT: "^(Pprinter.name2str m.name), heap)) heaps
	(*print_formset "\n\n Failed Heap:\n" [sheap]    *)
      )
  | _ -> 
  let exec n sheaps = 
    let sheaps_noid=fst sheaps in
    Rlogic.kill_all_exists_names sheaps_noid;
    if symb_debug() then Format.printf "Output to %i with heap@\n   %a@\n" (node_get_id n) (string_ts_form (Rterm.rao_create ())) sheaps_noid;
    execute_stmt n sheaps in 
  let execs n sheaps = List.iter (exec n) sheaps in 
(*  let minfo=node_get_method_cfg_info n in *)
  let succs=node_get_succs n in
  let id_clone h = (form_clone (fst h), snd h) in 
  let execs_one sheaps = 
    match succs with 
      [s] -> execs s sheaps 
    | _ -> assert false in
  let exec_one sheaps = 
    match succs with 
      [s] -> exec s sheaps 
    | _ -> assert false in
  if symb_debug() then Format.printf "@\nExecuting statement:@ %s%!" (Pprinter.statement2str stm.skind); 
  if symb_debug() then Format.printf "@\nwith heap:@\n    %a@\n@\n%!"  (string_ts_form (Rterm.rao_create ())) sheap_noid;
    (match stm.skind with 
      | Label_stmt l -> 
	  (*  Update the labels formset, if sheap already implied then fine, otherwise or it in. *)
	  (let id = node_get_id n in 
	  try
	    if symb_debug() then Format.printf "@\nPre-abstraction:@\n    %a@."  (string_ts_form (Rterm.rao_create ())) sheap_noid;
	    let sheaps_abs = Prover.abs !curr_abs_rules sheap_noid in 
	    if symb_debug() then Format.printf "@\nPost-abstractionc count:@\n    %d@."  (List.length sheaps_abs);
	    List.iter Rlogic.kill_all_exists_names sheaps_abs;
	    if symb_debug() then List.iter (fun sheap -> Format.printf "@\nPost-abstraction:@\n    %a@."  (string_ts_form (Rterm.rao_create ())) sheap) sheaps_abs;

	    let formset = (formset_table_find id) in 
	    if symb_debug() then (
               Format.printf "Testing inclusion of :@    %a" 
		  (Debug.list_format "@\n" (string_ts_form (Rterm.rao_create ()))) sheaps_abs;
               print_formset "in " (remove_id_formset formset)
	     );

	    let sheaps_with_id = add_id_formset sheaps_abs in
	    let sheaps_with_id = List.filter 
		(fun (sheap2,id2) -> List.for_all
		    (fun (form,id) -> 
		      if check_implication !curr_logic (form_clone sheap2) form  then (add_transition_TS (sheap,Pprinter.statement2str stm.skind,(form,id));false) else true)
		    formset;
		) sheaps_with_id in
	    List.iter (fun h ->
			 add_transition_TS (id_clone sheap,Pprinter.statement2str stm.skind, id_clone h)) sheaps_with_id;
	    formset_table_replace id (sheaps_with_id @ formset);
	    execs_one (List.map id_clone sheaps_with_id)
	  with Contained -> if symb_debug() then Printf.printf "Formula contained.\n")
      | Identity_stmt (n,id,ty) -> 
	  let h=exec_identity_stmt  n id ty (fst sheap) in
	  let h=add_id_form h in
	  add_transition_TS (id_clone sheap,Pprinter.statement2str stm.skind,id_clone h);
	  exec_one h 
      | Identity_no_type_stmt(n,id) -> assert false (*exec_identity_no_type_stmt sheap*)
      | Assign_stmt(v,e) -> 
	  let hs=(exec_assign_stmt  v e sheap n) in
	  let hs=add_id_formset hs in
	  List.iter (fun h ->
		       add_transition_TS (id_clone sheap,Pprinter.statement2str stm.skind,id_clone h)) hs;
	  execs_one hs
      | If_stmt(e,l) ->
	  let sheap2 = (form_clone (fst sheap), snd sheap) in 
	  (match succs with
	  | [s1;s2] -> 
	      (match s1.nd_stmt.skind with
	      | Label_stmt l' when l'=l -> 
		  let cc_h=(conj_convert (expression2pure e) (fst sheap)) in
		  exec s1 (cc_h, snd sheap);
		  let cc_h2=(conj_convert (expression2pure (negate e)) (fst sheap2)) in
		  exec s2 (cc_h2,snd sheap2)
	      | _ -> 
		  let cc_h=(conj_convert (expression2pure (negate e)) (fst sheap)) in
		  exec s1 (cc_h,snd sheap);
		  let cc_h2=(conj_convert (expression2pure e) (fst sheap2)) in
		  exec s2 (cc_h2,snd sheap2)
	      )
	  | _ -> assert false )
      | Goto_stmt _ | Nop_stmt  -> exec_one sheap
      | Ret_stmt v (* I treat this like return *) 
      | Return_stmt v -> 
	  let h=exec_return_stmt stm v (fst sheap) in
	  let h=add_id_form h in
	  add_transition_TS (id_clone sheap,Pprinter.statement2str stm.skind, id_clone h);
	  exec_one h
      | Invoke_stmt ie -> 
	  let hs=(exec_invoke_stmt ie sheap n) in
	  let hs=add_id_formset hs in
	  List.iter (fun h -> 
		       add_transition_TS (id_clone sheap,Pprinter.statement2str stm.skind,id_clone h)) hs;
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

    let meth_initial_form_noid = convert meth_initial_form in
    let meth_initial_form = add_id_form meth_initial_form_noid in 
    add_transition_TS (meth_initial_form,"METHOD: "^(Pprinter.name2str m.name), meth_initial_form);
    let meth_initial_formset =  [meth_initial_form] in
    let meth_final_formset_noid = [convert spec.post] in 
    let meth_final_formset = add_id_formset meth_final_formset_noid in
    if symb_debug () then print_formset ("\n"^(Pprinter.name2str m.name)^" init_form=") [meth_initial_form_noid] ;
    if symb_debug () then print_formset ("\n"^(Pprinter.name2str m.name)^" final_form=") meth_final_formset_noid ;
    let minfo=Cfg.mcfginfo_tbl_find (key_method m) in
    let start_node=method_cfg_info_get_start_node minfo in
    let end_node=method_cfg_info_get_exit_node minfo in
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
  if symb_debug() then Format.printf "\n\n %s = [" s;
  List.iter (fun n -> if symb_debug() then Format.printf " %i " (node_get_id n) ) l;
  if symb_debug() then Format.printf " ]\n\n"











(* implements a work-list fidex point algorithm *)
(* the queue qu is a list of pairs [(node, expression option)...] the expression
is used to deal with if statement. It is the expression of the if statement is the predecessor
of the node is a if_stmt otherwise is None. In the beginning is always None for each node *)
let compute_fixed_point (f : Jparsetree.jimple_file) 
(apfmap : logic Specification.ClassMap.t) (lo : logic) (abs_rules : logic)
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
  let lo = try let x=Specification.ClassMap.find cname apfmap in x with Not_found -> lo in
  curr_logic:= lo;
  curr_abs_rules:=abs_rules;
  compute_icfg mdl;
  create_program_variables mdl; 
  initialize_node_formsets mdl fields cname;  
(*  HACK HACK HACK:  
   This is so that the exist vars are dealt with correctly between verification of body, and use for calls. *)
  curr_static_methodSpecs:=sspecs;
(* HACK over *)
  worklist := List.filter (fun n -> (if symb_debug() then print_node n); match n.nd_kind with Start_node -> (if symb_debug() then Printf.printf "Start node %i\n" (node_get_id n));true | _ -> false) (icfg_nodes2list mdl);
  while (!worklist<>[]) do 
    let v=List.hd !worklist in
    worklist := List.tl !worklist;
    List.iter (fun f -> execute_stmt v f) (formset_table_find (node_get_id v));
    if symb_debug() then Printf.printf "\nEnd execution of node %i \n" (node_get_id v)
  done 
(*  if !Config.dotty_print then print_file_dotty "conf_node" (icfg_nodes2list mdl);*)
(*  List.iter (fun m -> check_post sspecs_prog m lo cname) mdl*)

let formset_entry_to_dot_label h1 =
  Str.global_replace (Str.regexp "\\\\n") "\\l" (String.escaped (Debug.toString (string_ts_form (Rterm.rao_create ())) (fst h1))) 

let pp_dotty_transition_system () =
  let printed = ref [] in
  let foname="execution.dot" in
  let dotty_outf=open_out foname in
  let pp_forms_node (h1,_,h2) =
    if not (List.mem (snd h1) !printed) then 
      let hstr1=formset_entry_to_dot_label h1 in 
      Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l]\n" (snd h1) hstr1;
      printed:=(snd h1)::!printed
    else ();
    if not (List.mem (snd h2) !printed) then 
      let hstr2=formset_entry_to_dot_label h2 in 
      Printf.fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l]\n" (snd h2) hstr2;
      printed:=(snd h2)::!printed;
  in
  if symb_debug() then Printf.printf "\n Writing transition system file execution.dot  \n";
  Printf.fprintf dotty_outf "digraph main { \nnode [shape=box,  labeljust=l];\n";
  List.iter pp_forms_node ((List.filter (fun (_,l,_) -> not((String.sub l 0 5)="ERROR" || (String.sub l 0 5)="EXIT:")) (get_transition_system ())));
  List.iter (fun (n1,l,n2) ->
	       if (String.sub l 0 7)="METHOD:" then
		 let i=get_counter_TS () in
		 inc_counter_TS();		 
		 Printf.fprintf dotty_outf "\n state%i[label=\"%s\", color=green,  style=filled]\n" i l;
		 Printf.fprintf dotty_outf "\n state%i -> state%i" i (snd n1); 
	       else if String.length l > 11 && (String.sub l 0 11)="ERROR EXIT:" then
		 let i=get_counter_TS () in
		 inc_counter_TS();		 
		 Printf.fprintf dotty_outf "\n state%i[label=\"%s\\n%s\", color=red,  style=filled]\n" i l (formset_entry_to_dot_label n2);
		 Printf.fprintf dotty_outf "\n state%i -> state%i" (snd n1) i; 
	       else if (String.sub l 0 6)="ERROR:" then
		 let i=get_counter_TS () in
		 inc_counter_TS();		 
		 Printf.fprintf dotty_outf "\n state%i[label=\"ERROR\", color=red,  style=filled]\n" i ;
		 Printf.fprintf dotty_outf "\n state%i -> state%i [label=\"%s\"]" (snd n1) i (String.sub l 6 (String.length l -6)) ; 
	       else if (String.sub l 0 5)="EXIT:" then
		 let i=get_counter_TS () in
		 inc_counter_TS();		 
		 Printf.fprintf dotty_outf "\n state%i[label=\"%s\\n%s\", color=green,  style=filled]\n" i l (formset_entry_to_dot_label n2);
		 Printf.fprintf dotty_outf "\n state%i -> state%i" (snd n1) i; 
	       else
		 Printf.fprintf dotty_outf "\n state%i -> state%i[label=\"%s\"]" (snd n1) (snd n2) l
	    ) (get_transition_system ()); 
  Printf.fprintf dotty_outf "\n\n\n}";
  close_out dotty_outf
