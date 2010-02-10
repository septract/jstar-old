(******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)

open Prover_types

open Vars
open Misc
open Pterm
open Rterm
open Rlogic
open Plogic
open Debug 


let prover_counter_example : ts_sequent list ref = ref []
let print_counter_example ()  = 
  Format.printf "Needed to prove:@   @[%a@]@\n@\n"
    (Debug.list_format "\nor" string_ts_seq)
    !prover_counter_example

let pprint_counter_example ppf () = 
  Format.fprintf ppf "Needed to prove:@   @[%a@]@\n@\n"
    (Debug.list_format "\nor" string_ts_seq )
    !prover_counter_example


let pprint_proof chan = 
  let s = Buffer.contents buffer_dump in 
  output_string chan s

let string_of_proof () =
  Buffer.contents buffer_dump

exception Failed_eg of ts_sequent list

(* frame, P,S |- P',S' *)

let filter_eq_eq pl = 
  let ret = List.filter (fun x -> match x with EQ(r1,r2) -> not (rep_eq r1 r2) | _ -> true) pl in
  ret



(* if sequent matches, then replace with each thing  in the sequent list *)
(*
type sequent_rule = representative psequent * (representative psequent list list) * string * (representative pform) * (where list)
*)


let string_pseq ppf (g,l,r) = 
  Format.fprintf ppf "%a@ | %a@ |- %a" 
    Plogic.string_form g 
    Plogic.string_form l
    Plogic.string_form r

let string_psr ppf (sr :sequent_rule) : unit = 
    match sr with 
      (conclusion, premises, name, (without1,without2), where) ->
	Format.fprintf ppf 
	  "rule %s:@\n%a@\n%a@\nwithout@\n %a@ |- %a@\n%a"
	  name
	  string_pseq conclusion
	  (Debug.list_format_optional "if\n " " or " (Debug.list_format ";" string_pseq)) premises
	  string_form without1
	  string_form without2
	  (Debug.list_format_optional "where" ";" string_where) where
	  

let mk_seq_rule (mat_seq,premises,name) = 
  mat_seq,premises,name,([],[]),[]


type rewrite_entry =  (args list * args * (pform) * (where list) * (pform) * string * bool) list

(* rules for simplifying septraction need defining as well *)


type external_prover = (pform -> pform -> bool)  * (pform -> args list -> args list list)

let default_pure_prover = 
  (fun x y -> (*Printf.printf "Assume \n %s \nProve\n %s \n" 
      (Plogic.string_form x) 
      (Plogic.string_form y);*)
    match y with 
      [P_PPred("true",_)] -> true 
    | _ -> false) , 
  (fun x y -> [])

type logic = tactical * Rlogic.rewrite_map * external_prover

let empty_logic : logic = (Rules []),Rterm.rm_empty, default_pure_prover

(* Running the prover with default_tactical rules *)
(* should be equivalent to running the old implementation *)
(* of the prover on rules *)
let default_tactical rules = Repeat (Rules rules)

let external_proof ep ts pl_assume rs p_goal = 
  false
(*   disabled as going to be part of the rterm world seemlessly.*)
(*
  let hash = (rao_create ()) in
  let interpr = Rhash_args.create 30 in
  let out_form = ts_form_plain_pform_rs interpr hash (ts,pl_assume) rs in
  let evs = ev_form out_form vs_empty in
  let subst = subst_kill_vars_to_fresh_prog evs in 
  let out_form = Plogic.subst_pform subst out_form in 
  let query = (fst ep) out_form in 		
  let (pl,sl,cl),interp = p_goal in
  if sl != [] || cl != [] then raise No_match else ();
  let tryform = form_to_plain_pform interpr rs hash ts pl in 
  (*if !(Debug.debug_ref) then 
     Printf.printf "External proof\n Assume \n %s \nProve\n %s \n" 
      (Plogic.string_form out_form) 
      (Plogic.string_form tryform);*)
  query tryform
*)


let rec find_no_match f l =
  let rec fnm_inner f r l =
  match l with 
    [] -> raise No_match
  | x::l -> try f x (r@l) with No_match -> fnm_inner f (x::r) l
  in fnm_inner f [] l 

let rec unify_form_at ts (pa : pform_at) (f : form) (use_ep) (interp : var_subst) 
    (remove : bool)
    (cont : var_subst * form -> 'a) : 'a =
  let  pl,sl,cl = f in 
  let rs = rv_form f  Rset.empty in 
  match pa with 
    P_SPred (name1,al1) ->
      find_no_match  
	(fun (SPred(name2,rl2)) sl2 
	  ->
	    if name1=name2 then unifies_list ts al1 rl2 interp 
		(fun interp -> cont (interp, (pl,(if remove then sl2 else sl),cl)))
	    else raise No_match
	)  
	sl
  | P_EQ(a1,a2) ->
  (try
      find_no_match
	(fun p pl2 -> 
	  match p with 
	    EQ(r1,r2) -> 
	      (try 
		(unifies_list ts [a1;a2] [r1;r2] interp 
		   (fun interp -> cont (interp, ((if remove then pl2 else pl),sl,cl))))
	      with No_match ->
		(unifies_list ts [a1;a2] [r2;r1] interp 
		   (fun interp -> cont (interp, ((if remove then pl2 else pl),sl,cl)))))
	  | _ -> raise No_match
	)
	pl
	with No_match when use_ep != None -> 
	  (try 
	    Rterm.unifies_eq ts (rv_form (pl,sl,cl) (Rset.empty)) a1 a2 interp (fun interp -> cont (interp, (pl,sl,cl)))
	  with No_match ->  (* Try to prove guard equality with external prover *) 
	    (match use_ep with 
	      Some ep -> 
(*		Printf.printf "Trying ep";*)
(**TODO		if not (Rlogic.closes interp [pa]) then raise No_match;
		let result = external_proof ep ts pl rs (pform_convert ts interp [pa] false) in 
		if result then cont (interp,f) else *)raise No_match
	    | None -> raise No_match  (* This is unreachable *))
	  )
  )
  | P_NEQ(a1,a2) -> 
      (try
	(
	 find_no_match
	   (fun p pl2 -> 
	     match p with 
	       NEQ(r1,r2) -> 
		 (try 
		   (unifies_list ts [a1;a2] [r1;r2] interp 
		      (fun interp -> cont (interp, ((if remove then pl2 else pl),sl,cl))))
		 with No_match ->
		   (unifies_list ts [a1;a2] [r2;r1] interp 
		      (fun interp -> cont (interp, ((if remove then pl2 else pl),sl,cl)))))
	     | _ -> raise No_match
	   )
	   pl
	)
      with No_match ->
	(match use_ep with 
	  Some ep -> 
	    if not (Rlogic.closes interp [pa]) then raise No_match;
	    let result = external_proof ep ts pl rs (pform_convert ts interp [pa] false) in 
	    if result then cont (interp,f) else raise No_match
	| None -> raise No_match
	)
      )
  | P_PPred(name1,al1) ->
      (try find_no_match  
	  (fun pf pl2 
	  ->
	    match pf with 
	      PPred(name2,rl2) -> 
		if name1=name2 then unifies_list ts al1 rl2 interp 
		    (fun interp -> cont (interp, ((if remove then pl2 else pl),sl,cl)))
		else raise No_match
	    | _ -> raise No_match
	) pl
      with No_match ->
	  (match use_ep with 
	      Some ep -> 
		if not (Rlogic.closes interp [pa]) then raise No_match;
		let result = external_proof ep ts pl rs (pform_convert ts interp [pa] false ) in 
		if result then cont (interp,f) else raise No_match
	    | None -> raise No_match
	  )	
      )
  | P_Garbage -> 
      find_no_match 
       (fun cf cl2 
           -> 
             match cf with 
               Garbage -> cont (interp, (pl,sl,(if remove then cl2 else cl)))
             | _ -> raise No_match

       ) cl
  |  P_Or (f1,f2) -> (
      try 
        match_form ts f1 f use_ep interp remove cont 
      with No_match -> 
	match_form ts f2 f use_ep interp remove cont )
  | _ -> unsupported ()


and match_form ts (pattern : pform) (target : form) (use_ep) (interp : var_subst) remove (cont : var_subst * form -> 'a) : 'a = 
  match pattern with 
    [] -> cont (interp,target)
  | pa::pf -> 
      unify_form_at ts pa target use_ep interp remove
	(fun (interp,target) -> match_form ts pf target use_ep interp remove cont)
 

(* assumes pattern is already ground.  Probably should fix this*)
let rec contains ts (pattern : pform)  (target : form) use_ep interp : (var_subst option)
    =  
  try 
    if Rterm.ts_debug then Format.fprintf !dump "Contains:@ %a@\n" Plogic.string_form pattern; 
    match_form ts pattern target use_ep interp false (fun (interp,_) -> if Rterm.ts_debug then Format.fprintf !dump "Match@\n"; (Some interp))
  with No_match -> if Rterm.ts_debug then Format.fprintf !dump "No Match@\n" ; None



let arg_var_to_evar avar =
  match avar with 
    Arg_var evar -> evar
  | _ -> unsupported ()


let check_cxt where (context_evs,interp) ts = 
  if ts_debug then 
    Format.fprintf !dump "Checking context! %a@\n" string_rep_list_db (Rset.elements context_evs);
  let var_term_to_set varterm =
    match varterm with 
      Var vl -> vl
  in
  match where with
    NotInContext varterm ->
      let varset = var_term_to_set varterm in
      let b = not (vs_exists 
	     (fun var -> 
	       let r = (find_vs ts var interp) in 
	       if ts_debug then 
		 Format.fprintf !dump "For %a@\n" string_rep_db r;
	       Rset.mem r context_evs
	     ) 
	     varset
	  ) in 
      if ts_debug then 
	(if b then Format.fprintf !dump "Not found!@\n" else Format.fprintf !dump "Found! @\n");
      b
(*      not (vs_exists (fun var -> vs_mem (arg_var_to_evar (subst_var interp var)) context_evs) varset)*)
  | NotInTerm (varterm,args) -> 
      let varset = var_term_to_set varterm in
      let r,interp2 = add_term ts interp args false false in 
 (*     assert(interp2 = interp);  (* Shouldn't change the interpretation *) TODO Can't just structural equality*)
      let args_evs = rv_transitive r in
      not (vs_exists (fun var -> Rset.mem (find_vs ts var interp) args_evs) varset)
 

let check where (form,interp) ts = 
      let pl,sl,cl = form in 
      let context_evs = Rterm.accessible_rs ts in
      let context_evs = rv_spat_list sl context_evs in
      let context_evs = rv_comp_list cl context_evs in 
      let context_evs = rv_plain_list (List.filter (fun p -> match p with NEQ _ -> false | _ -> true) pl) context_evs in 
      let context_evs = rv_trans_set context_evs in
      check_cxt where (context_evs, interp) ts


let f2f ff = ([],ff,[]) 


(* CPS style backtracking pattern matcher *)
let apply_rule (rule : sequent_rule) (seq : ts_sequent)  ep : ts_sequent list list= 
    match rule with (* ignores right hand plains in sequent match *)
      (pff,pfl,pfr),premises,name,without,wherelist ->
	(*Printf.printf "\n\n Trying rule %s\n" name;*)
	match seq with
	  ts,(ff,afl,fr) ->
	    (* match right bit *)
	    match_form ts pfr fr None Rterm.empty_vs true
	      (
	    fun (interp,fr) ->
              (* match left_bit *)
	      match_form ts pfl afl (Some ep) interp true
		   ((* match frame bit *)
		    fun (interp,fl) ->
		      match_form ts pff (f2f ff @@@ fl) None interp true
			(fun (interp,_) -> 
			  (* check if there is a without clause, and if it is matched
			     If it is matched, then throw no_match as we don't want to apply*)
			  if fst without != []  && 
			    (contains ts (fst without) ((f2f ff)@@@ afl) (Some ep) interp != None) 
			  then (raise No_match );
			  (* Check on the right hand side too *)
			  if snd without != []  && 
			    (contains ts (snd without) ((f2f ff)@@@ afl @@@ fr) (Some ep) interp != None) 
			  then (raise No_match );
			  (* check where clauses are satisfied *)
			  if List.for_all (fun where -> check where (f2f ff@@@fl,interp) ts) wherelist 
			  then () else raise No_match ;
			  match premises with 
(* OPtimisation?*) 	    [[premise]] -> 
                              let newvars = vs_diff (fv_psequent premise) (fv_psequent (pff,pfl,pfr)) in 
			      let subst = (subst_kill_vars_to_fresh_exist newvars) in 
			      let premise = subst_psequent subst premise in 
			      let premise : sequent = psequent_convert ts interp premise in 
			      let sequent = Rlogic.sequent_join premise (ff, fl, fr) in
			      vs_iter (fun nv -> Rterm.kill_var ts (match Pterm.subst_var subst nv with Arg_var(v) -> v | _ -> unsupported ())) newvars;
			      if !debug_ref then Format.fprintf !dump "Rule: %s@\n@." name else ();  
			      [[ts,sequent]]
			  | _ ->
			      (let result = List.map (map_option (fun premise ->
  				(* only need do union at as contradiction caught on substitution *)
				(* freshen premise *)
				let newvars = vs_diff (fv_psequent premise) (fv_psequent (pff,pfl,pfr)) in 
				let premise = subst_psequent (subst_freshen_vars newvars)  premise in 
				try let premise : sequent = psequent_convert ts (freshening_vs interp) premise in
				let sequent = Rlogic.sequent_join premise (ff, fl, fr) in
				let ts,subst =(clone ts (Rlogic.rv_sequent sequent) false) in 
				let sequent = subst_sequent subst sequent in  
				Some (ts,sequent) 
				with Success -> None
								))
				  premises in 
			      if !debug_ref then Format.fprintf !dump "Rule: %s@\n@." name else ();  
			      result
			      )
			)
		   )
	      )
		   

let rec apply_rule_list_once (rules : sequent_rule list) (seq : ts_sequent) ep : ts_sequent list list
    =
  match rules with 
    [] -> raise No_match
  | rule::rules ->
      try 
	(*Printf.printf "Trying rule: %s\n" (match rule with (pff,pfl,pfr),premises,name,without,wherelist -> name);*)
(*	Printf.printf "Trying rule: \n%s\n" (string_psr rule);*)
	apply_rule rule seq ep
      with No_match -> apply_rule_list_once rules seq ep


(*  Removed done by ts now.

let rec subs_eqs_seq seq =
   match seq with 
   | framed,(plain,left),(plainright, right) ->
       match subst_eqs plain with 
	 None -> seq
       | Some (plain,subs,usedeqs) -> 
	   sequent_join 
	     (subs_eqs_seq (subst_sequent subs (framed,(plain,left),(plainright, right))))
	     ([],(usedeqs,[]),([],[]))
*)






(* Changed code to erase terms on both abstraction and non abstraction rewrites. *)


let rec rewrites_sequent_inner rwm (ts,seq) rewrite_track ep abs redun =
  Format.fprintf !dump "@\n@\n====================Start rewrites======================" ;
  try 
    let ep = ep in  (* give ep the correct assumption *)
    let rs = rv_sequent seq in 
    let (fsl,fl,fr) = seq in 
    let f (interp,(withoutc,wherec,withc),tid) = 
       let si = 
	 if withc = [] then 
	   Some interp 
	 else contains ts withc (fl@@@fr) (Some ep) interp in 
       match si with
	 None -> None 
       | Some interp -> 
	   if 
	     (withoutc = [] 
	       || (contains ts withoutc (fl@@@fr) (Some ep) interp) = None)
	       && 
	     (wherec = [] 
	       || List.for_all 
		   (fun whc -> 
(* let rv_trans_set_fb fb rs rs_base : rset_t = *)
		     let fbtids = TIDset.add tid !rewrite_track in 
		     let contextevs = Rterm.accessible_rs_fb fbtids ts in 
		     let contextevs = rv_trans_set_fb fbtids ((rv_form fl) (rv_spat_list fsl Rset.empty))  contextevs in 
		     check_cxt whc (contextevs, interp) ts) wherec) then Some interp else None
(*Old code that didn't perform unification on if/with clause. 

       (withc = [] || contains ts withc (fl@@@fr) (Some ep) interp) 
    && (withoutc = []  || not (contains ts withoutc (fl@@@fr) (Some ep) interp))
    && (wherec = [] || List.for_all (fun whc -> check_cxt whc (Rterm.accessible_rs_fb !rewrite_track ts, interp) ts) wherec )*)
    in 
    let subst = rewrite_ts ts rwm rewrite_track rs f redun in 
    try 
      let ts_seq = (ts,subst_sequent subst seq) in 
      if true || !(Debug.debug_ref) then Format.fprintf !dump "Rewritten to@\n %a@\n" string_ts_seq ts_seq;
(*      if abs then (
	Rterm.kill_term_set ts !rewrite_track; 
        if Rterm.ts_debug then Format.printf "Tidied after rewrites@\n %a" string_ts_db ts
	    ) ;  *)
      rewrites_sequent_inner rwm ts_seq rewrite_track ep abs redun 
    with Success -> 
      (ts,true_sequent)
  with No_match -> 
    if Rterm.ts_debug then Format.fprintf !dump "Finished rewrites@\n %a" string_ts_db ts;
(*    if abs then (
      Rterm.kill_term_set ts !rewrite_track;    
      if Rterm.ts_debug then Format.printf "Tidied after rewrites@\n %a" string_ts_db ts
	  ) ;*)
    Rterm.kill_term_set ts !rewrite_track;    
    if Rterm.ts_debug then Format.fprintf !dump "Tidied after rewrites@\n %a" string_ts_db ts;
    Format.fprintf !dump "=================Finished rewrites====================@\n@\n" ;
    (ts,seq)


let rewrites_sequent rwm ep abs redun (ts,seq) =
  let rewrite_track = ref Rterm.TIDset.empty in 
  rewrites_sequent_inner rwm (ts,seq) rewrite_track ep abs redun



let mkOrLazy cp1 cp2 =
  try 
    let p1 = cp1 () in 
    try 
      let p2 = cp2 () in 
      Or(p1,p2)
    with Contradiction -> p1
  with Contradiction -> cp2 ()

let use_neq ((pl,sl,cl) : form) neqs : form =
  match cl with 
  | [] -> (pl,sl,cl) 
  | _ -> 
      let neqs = map_option (fun p -> match p with NEQ(x,y) -> Some (x,y) | _ -> None) (pl @ neqs) in
      let rec f c () = 
	match c with 
	  Or(c1,c2) -> 
	    mkOrLazy (f c1) (f c2) 
	| Form(pl,sl,cl) -> 
	    if List.exists 
		(fun p -> 
		  match p with 
		    EQ(r1,r2) -> List.exists 
			(fun (r3,r4) -> (rep_eq r1 r3 && rep_eq r2 r4) || (rep_eq r1 r4 && rep_eq r2 r3) ) neqs 
		  | NEQ(r1,r2) -> rep_eq r1 r2
		  | _ -> false) 
		pl  
	    then raise Contradiction else c
	| c -> c in
      (pl,sl,List.map (fun c -> f c ()) cl)
 

let sequent_use_neqs (ts,(f1,f2,f3)) =
  (ts,(f1,use_neq f2 [], f3))  


let sequents_use_neqs =
  List.map sequent_use_neqs


(*
let rec remove_emps (sp : spatial list) (emps : emp_rule list ) (p : plain list) : plain list  * spatial list
    =
  match emps with 
    [] -> p,sp
  | (es,ep,_)::emps ->
      let (p,sp) = 
	List.fold_right 
	  (fun (s : spatial) ((plain : plain list),(sp : spatial list))  -> 
	    try 
	      let interp =  unify_spat es s empty in
	      ((List.map  (subst_plain interp) ep) @ plain),sp
	    with No_match -> (plain,s::sp))
	  sp (p,[])
	  (* match, empty, add plain properties *)
      in remove_emps sp emps p


let remove_emps_seq emps (seq : sequent) : sequent list =
  let (frame,(pl,sl),(pr,sr)) = seq in
  let (pl,frame) = remove_emps frame emps pl in 
(*  try *)
    let (pl,sl) = remove_emps sl emps pl in 
    let (pr,sr) = try remove_emps sr emps pr with Contradiction -> raise Failed in 
    [(frame,(pl,sl),(pr,sr))]
(*  with Contradiction -> [] *)

let remove_emps_seq_list emps (seqs : sequent list) : sequent list =
  List.flatten (List.map (remove_emps_seq emps) seqs)
*)


(* Start of plain prover 
This is a pretty poor prover at the moment. 
*)
let plain_false = [[],[],False]

let rec plain_list_conjunction pl1 pl2 =
  match pl1 with 
    [] -> pl2
  | p1::pl1 -> List.map (fun p2 -> p1 @ p2) (plain_list_conjunction pl1 pl2)
(*
let apply_plain_rule (sp,p,_) f plain=
  List.fold_left 
    (fun plain (interp,_) -> 
      (plain_list_conjunction 
	 (List.map 
	    (map_option 
	       (fun p -> 
		 try 
		   Some (subst_plain interp p)
		 with Contradiction ->
		   None
		   )
	       ) p)) plain)
    plain
    (match_spat_all sp f empty)

let apply_plain_rules plain_rules f plain=
  let rec inner_apply_plain_rules plain_rules f plain =
    match plain_rules with 
      [] -> plain
    | pr :: plain_rules ->
	(inner_apply_plain_rules plain_rules f (apply_plain_rule pr f plain))
  in 
  try inner_apply_plain_rules plain_rules f [plain]
  with No_match -> [plain]

let rec find_first f ls rs=
  match ls with 
    [] -> raise Not_found
  | l::ls -> if f l then l , (ls@rs) else find_first f ls (l::rs)

let rec apply_plain_exists_elim (pl1,pl2) = 
  let recs,pl1 = List.partition (fun p -> match p with EQ(Arg_record(_), Arg_record(_)) -> true | _ -> false) pl1 in
  let rec f recs pl1 =  
    match recs with
      [] -> pl1
    | r::recs -> 
	try (
	  match r with 
	    EQ(Arg_record(fld1), Arg_record(fld2)) ->
	      f recs (record_eqs fld1 fld2 pl1 true)
	  | _ -> unsupported ()
	 ) with Failed -> f recs (r::pl1) in
  let pl1 = f recs pl1 in 
  try 
    let EQ(Arg_var v,a),pl2 = find_first (fun p -> match p with EQ(Arg_var(EVar (_,_)),y) -> true | _ -> false ) pl2 [] in 
    let sub = add v a empty in 
    apply_plain_exists_elim (usedEQ(Arg_var v,a)::(List.map (subst_plain sub) pl1),List.map (subst_plain sub) pl2)
  with Not_found -> (pl1,pl2)
*)

let apply_plain_simp  (pl1,pl2) = 
  let pl1 = filter_eq_eq pl1 in
  let pl2 = filter_eq_eq pl2 in 
  let pl2 = List.filter (fun p -> not (List.exists (fun x -> plain_eq x p) pl1) ) pl2 in
  (*apply_plain_exists_elim*) (pl1,pl2)

let apply_plain_prove_2 plain_rules ep ((ts,(f,s,c)) : term_structure * (spatial list * spatial list * composite list)) (pl1 : plain list) (pl2 : plain list) (p_goal) cl interp hash  =
  (*Printf.printf "Trying plain prover\n";*)
  match apply_plain_simp (pl1,pl2),p_goal with
    (pl1,[]),[] -> [ts,(f,(pl1,s,c),([],[],[]))]
  | (pl1,pl2), p_goal -> raise Failed
    (* TODO: Need to do something here for calling SMT*)
(*
      let rs1 = rv_form (pl1,s,c) (rv_spat_list f Rset.empty) in   
      let rs2 = rv_plain_list pl2 (rv_comp_list cl Rset.empty) in   
      let p1,p2 = ts_sequent_plain_pform interp (ts,(pl1,pl2)) hash rs1 rs2 in
      let rs = rv_trans_set (rv_form (pl1,s,c) (rv_spat_list f Rset.empty)) in 
      let p_assume = composite_list_is_plain interp rs hash ts c in 
      let p_assume = match p_assume with None -> [] | Some x -> x in  
      if true || !(Debug.debug_ref) then Format.fprintf !dump "Ask external prover to complete proof.@\n";
      let p1 = p1 @ p_assume in
      let p2 = p2 @ p_goal in
      let evs = ev_form p1 vs_empty in
      let subst = subst_kill_vars_to_fresh_prog evs in 
      let b = (fst ep) (Plogic.subst_pform subst p1) (Plogic.subst_pform subst p2) in
      if b then [ts,(f,(pl1,s,c),([],[],[]))] else raise Failed
*)


let apply_plain_prove plain_rules ep ((ts,(f,s,c)) : term_structure * (spatial list * spatial list * composite list)) (pl1 : plain list) (pl2 : plain list) =
  let hash = (rao_create ()) in 
  let interp = Rhash_args.create 30 in 
   apply_plain_prove_2 plain_rules ep (ts,(f,s,c)) pl1 pl2 [] [] interp hash 

let apply_plain_prove_contra plain_rules ep ((ts,(f,s,c)) : term_structure * (spatial list * spatial list * composite list)) (pl1 : plain list) =
  let hash = (rao_create ()) in 
  let interp = Rhash_args.create 30 in 
   apply_plain_prove_2 plain_rules ep (ts,(f,s,c)) pl1 [] [P_False] [] interp hash 


(*      let pl1l = apply_plain_rules plain_rules (f@s) pl1  in 
      let rec plain_prove_inner pl1l = 
	match pl1l with 
	  [] -> []
	| pl1::pl1l ->
	    match apply_plain_simp (pl1,pl2) with
	      (pl1,[]) -> [f,(pl1,s,c),([],[],[])] @ plain_prove_inner pl1l
	    | (pl1,pl2) ->      
		if !debug_ref then Printf.printf "Prove %s | %s| %s  ===>  %s\n" 
		    (string_spatial_list f) (string_spatial_list s) 
		    (string_plain_list pl1) (string_plain_list pl2);
		raise Failed (*[(f,(pl1,s),(pl2,[]))] @ (plain_prove_inner pl1l)*) in
      plain_prove_inner pl1l*)
(* End of plain prover *)

(*
let or_to_list form = 
  let rec inner_or_list form_list sl_acc form_done flag = 
    match form_list with
    | [] -> if flag then form_done else raise No_match
    | (pl,[])::form_list -> inner_or_list form_list [] ((pl,sl_acc)::form_done) flag
    | (pl,Or(f1,f2)::sl)::form_list ->
	inner_or_list ((f1 &&& (pl,(sl_acc@sl))) :: (f2 &&& (pl,sl_acc@sl)) :: form_list) [] form_done true
    | (pl,s::sl)::form_list -> inner_or_list ((pl,sl)::form_list) (s::sl_acc) form_done flag in
  inner_or_list [form] [] [] false
*)


let apply_rule_or_left seq =
  match seq with 
    ts,(f,(pl,sl,cl),f3)
    ->   
  (let rec or_inner cl cl2 = 
    match cl with 
      (Or(f1,f2))::cl -> 
	let seq2 = (f, (pl,sl,f2::cl@cl2), f3) in 
	let rvs = Rlogic.rv_sequent  seq2 in 
	let ts2,subs = clone ts rvs false in 
	let seq2 = subst_sequent subs seq2 in 
	[ts,(f, (pl,sl,f1::cl@cl2), f3); ts2,seq2]
    | c :: cl -> or_inner cl (c::cl2)
    | [] -> raise No_match
  in or_inner cl [])
 
(*let apply_rule_flatten seq = 
  let rec inner seq cl' =  
    let (ts,(f,(pl,sl,cl),f3)) = seq in 
    match cl with 
      [] -> (ts,(f,(pl,sl,cl'),f3))
    | Form(pl1,sl1,cl1) :: cl -> inner (ts,(f,(pl1@pl,sl1@sl,cl1@cl),f3)) cl' 
    | c::cl -> inner (ts,(f,(pl,sl,cl),f3)) (c::cl')
  in  inner seq []*)

let apply_rule_flatten seq = 
  let rec inner (pl,sl,cl) cl' =  
    match cl with 
      [] -> (pl,sl,cl')
    | Form(pl1,sl1,cl1) :: cl -> inner (pl1@pl,sl1@sl,cl1@cl) cl' 
    | c::cl -> inner (pl,sl,cl) (c::cl')
  in let (ts,(f,f1,f2)) = seq in
  (ts,(f,inner f1 [],inner f2 []))
	  

(* Very simple *)
let apply_rule_or_right seq =
  match seq with 
    ts,(f,f3,(pl,sl,cl))
    ->     
  let rec aror_inner cl cl2 =
  match cl with 
    (Or(c1,c2))::cl -> 
        if true || !(Debug.debug_ref)  then Format.fprintf !dump "Case split on or right!\n";
	let seq2 = (f,f3,(pl,sl,c2::cl2@cl)) in 
	let rvs = Rlogic.rv_sequent  seq2 in 
	let ts2,subs = clone ts rvs false in 
	let seq2 = subst_sequent subs seq2 in 
      [[ts,(f,f3,(pl,sl,c1::cl2@cl))];[ts2,seq2]]
  | c::cl ->  
      if true || !(Debug.debug_ref)  then Format.fprintf !dump "Not an or!\n";
      aror_inner cl (c::cl2)
  | [] -> raise No_match
  in aror_inner cl []


let rec sequent_subtract (ts,(fr,(p1,s1,c1),(p2,s2,c2))) = 
  let p2 = filter_eq_eq p2 in 
  let rec inner_seq_sub fr s1 s2 rs =
  match s1 with 
    [] -> (fr,rs,s2)
  | s::s1 -> (
      let (fs2,rs2) = List.partition (fun s' -> spat_eq s' s) s2 in
      match fs2 with 
	[] -> inner_seq_sub fr s1 (fs2@rs2) (s::rs)
      | f::fs -> 
	  inner_seq_sub (s::fr) s1 (fs@rs2) rs
     )
  in let (fr,s1,s2) = inner_seq_sub fr s1 s2 [] in 
  ts,(fr,(p1,s1,c1),(p2,s2,c2))

let rec sequents_subtract seqs = 
  List.map (sequent_subtract) seqs

let ask_the_audience ep ts p1 rs = 
  raise No_match
(* TODO: This should be dealt with Rterm. *)
(*
  if true || !(Debug.debug_ref) then Format.fprintf !dump "Query external prover@\n";
  let hash = (rao_create ()) in
  let interp = Rhash_args.create 30 in
  let out_form = ts_form_plain_pform_rs interp hash (ts,p1) rs in
  let evs = ev_form out_form vs_empty in
  let subst = subst_kill_vars_to_fresh_prog evs in 
  let out_form = Plogic.subst_pform subst out_form in 
  let query = (fst ep) out_form in 
  let b = query [P_False] in 
  if b then raise Contradiction;
  let terms_assoc = List.map (fun r -> pterm_rep interp rs hash r, r) (Rset.elements rs) in 
  let terms = List.map fst terms_assoc in 
  let congruence = (snd ep) out_form terms in 
  let eqs =
    List.fold_right 
      (fun terms eqs ->
	match terms with 
	  term::terms ->  
	    let r = List.assoc term terms_assoc in 
	    List.fold_right 
	      (fun term eqs-> 
		let r' = List.assoc term terms_assoc in 
		(r,r')::eqs
	      )
	      terms eqs
	| [] -> eqs
      )
      congruence [] in 
  match eqs with 
    [] -> raise No_match 
  | _ ->  make_equal ts eqs (empty_subst())
*)

(* let rec sequents_backtrack  f (seqss : ts_sequent list list) xs *)
let rec sequents_backtrack  f seqss xs
    =
  match seqss with 
    [] -> raise (Failed_eg xs)
  | seqs::seqss -> 
      try f seqs 
      with Failed ->  (if true || !(Debug.debug_ref) then Format.fprintf !dump "Backtracking!\n"); sequents_backtrack f seqss xs
      | Failed_eg x -> (if true || !(Debug.debug_ref) then Format.fprintf !dump "Backtracking!\n"); sequents_backtrack f seqss (x @ xs)

(* Wand on left rule *)
(* TODO
  find a wand    S * S'-* S''  (add some plain stuff to this)
  do frame inference  S |- S'  * F?   (* add coframe inference later ( see notes )*)
  rewrite to F * S''   
*)

let eqs_elim (ts_seq : ts_sequent) : ts_sequent =
  let find_string x = List.find 
      (function tid -> match !tid.term with 
	FTString _ -> true | _ -> false) 
      !x.terms in
  let find_record x = List.find 
      (function tid -> match !tid.term with 
	FTRecord _ -> true | _ -> false) 
      !x.terms in
  let (ts,(f,(pl,sl,cl),(pl2,sl2,cl2))) = ts_seq in 
  let eqs,pl = List.partition (fun p -> match p with EQ(_,_) -> true | _ -> false) pl in 
  if !debug_ref && eqs != [] then Format.fprintf !dump "Elim eqs : %a@\n" string_plain_list eqs;
  let eqs = List.map (fun p -> match p with EQ(x,y) -> (x,y) | _ -> unsupported ()) eqs in
  try 
    let subst = make_equal ts eqs (empty_subst ()) in 
    
    let rhs = 
      try 
	(List.fold_right
	   (fun p ps -> match p with 
	       EQ(x,y) -> (if rep_eq x y then ps
	       else 
		 try 
		   if find_string x = find_string y 
		   then 
		     (* If they had the same string, then they would
		     have the same representative.  So this control
		     path cannot be reached unless something is
		     wrong. *)
		     assert false 
		   else
		     (* We are trying to prove two different strings
		     have the same value, this is impossible.*)
		     raise Contradiction 
		 with Not_found -> (
		   try 
		     (match !(find_record x).term,!(find_record y).term with
		       FTRecord fld1, FTRecord fld2 -> 
			 let fl1,rl1=List.split fld1 in
			 let fl2,rl2=List.split fld2 in 
			 if fl1=fl2 then 
			   ((List.map (fun (x,y) -> EQ(x,y)) (List.combine rl1 rl2)) @ ps)
			 else raise Contradiction 
		     |  _ -> assert false)
		   with Not_found ->  p::ps)
		     )		     
	     | NEQ(x,y) -> 
		 (if rep_eq x y then raise Contradiction
		 else 
		   try 
		     if find_string x = find_string y 
		     then
		       (* Cannot happen as this requires them to have
		       same representative*)
		       assert false
		     else
		       (* The two equivalence classes contain
		       different strings, so the inequality must be
		       true. So filter can drop it. *)
		       ps
		   with 
		     (* We know nothing, so leave it there *)
		     Not_found -> p::ps)
	     | _  -> p::ps) 
	   pl2 [],
	 sl2,cl2) 	  
      with Contradiction ->  ([],[],[False])  in
    (ts, subst_sequent subst (f,(pl,sl,cl),rhs))
  with Contradiction -> raise Success 

let exists_elim_simple (ts_seq : ts_sequent) : ts_sequent =
  let (ts,(f,f1,f2)) = ts_seq in 
  let left_reps = rv_form f1 Rset.empty in
  let left_reps = rv_spat_list f left_reps in 
  let pl,sl,cl = f2 in 
  let eqs,pl = List.partition (fun p -> match p with EQ(_,_) -> true | _ -> false) pl in 
  let rec ees_inner eqs f f1 pl sl cl = 
    match eqs with
      [] -> (ts,(f,f1,(pl,sl,cl)))
    | EQ(r1,r2)::eqs -> 
	if rep_eq r1 r2 then ees_inner eqs f f1 pl sl cl
	else (
(*	Printf.printf "Trying %s=%s\n" (string_rep r1) (string_rep r2);*)
	try 
	  (try 
	     let subst = try_equal ts r1 r2 left_reps in
	     ees_inner (subst_plain_list subst eqs)
	       (subst_spatial_list subst f)
	       (subst_form subst f1)
	       (subst_plain_list subst (EQ(r1,r2)::pl))
	       (subst_spatial_list subst sl)
	       (subst_composite_list subst cl)
	  with Contradiction ->
	      (ts,(f,f1,([],[],[False]))))
	with Not_found -> unsupported ())
    | _ -> unsupported () (* Unreachable, because of partition above *)
  in ees_inner eqs f f1 pl sl cl

let apply_contradiction seq = 
  let _,(_,(_,_,cl),_) = seq in 
  if List.exists (fun c -> c=False) cl then None else Some seq
  
let tidy_sequents logic sequents =
  let rules,rwm,ep = logic in 
  (* Collapse Form in combined construct *)
  let sequents : ts_sequent list = List.map apply_rule_flatten sequents in
  (* substitute away equalities *)
(*  let sequents = map_option (fun seq -> try Some (subs_eqs_seq seq) with Success -> None) sequents in*)
  (* perform rewrite rules *)
(*  let sequents = List.map (rewrites_sequent rwm) sequents in*)
  (*  Filter empties  *)
(*  let sequents : sequent list = remove_emps_seq_list emps sequents in*)
  (* Remove records on right where possible *)
(*  let sequents = List.map simp_seq_with_record sequents in *)
  (* substitute away equalities *)
(*  let sequents = map_option (fun seq -> try Some (subs_eqs_seq seq) with Success -> None) sequents in*)
  Format.fprintf  !dump "Foo";
    let sequents : ts_sequent list = map_option (fun seq -> try Some (eqs_elim seq) with Success -> (if true || !(Debug.debug_ref) then Format.fprintf !dump "Success : %a\n" string_ts_seq seq; None)) sequents in 
(*  List.iter (fun seq -> Printf.printf "%s> %s\n" (String.make n '-') (string_ts_seq seq)) sequents;*)
  let sequents : ts_sequent list = List.map exists_elim_simple sequents in 
  (* perform rewrite rules *)
  let sequents = List.map (rewrites_sequent rwm ep abs false) sequents in
  let sequents = map_option apply_contradiction sequents in 
  (* Use neqs *)
  let sequents : ts_sequent list = sequents_use_neqs sequents in 
  (* perform rewrite rules *)
  let sequents = List.map (rewrites_sequent rwm ep abs false) sequents in 
  let sequents : ts_sequent list = List.map exists_elim_simple sequents in 
  let sequents : ts_sequent list = map_option (fun seq -> try Some (eqs_elim seq) with Success -> (if true || !(Debug.debug_ref) then Format.fprintf !dump "Success : %a\n" string_ts_seq seq; None)) sequents in 
  (*  Apply subtarction *)
  let sequents : ts_sequent list = sequents_subtract sequents in
(*  List.iter (fun seq -> Printf.printf "%s> %s\n" (String.make n '-') (string_ts_seq seq)) sequents;*)
	sequents		

let rec lifted_apply_tactic_till_fail logic abs failing seqs =
	let slim f s = let (_,r) = f s in r in
	let rec apply_tactic_till_fail logic failing seq =
	  (* check for base sequents *)
	  if true || !(Debug.debug_ref) then Format.fprintf !dump ">@[%a@]@\n@." string_ts_seq  seq;
	  match seq with 
	   | ts,(f,(p1,s1,c1),(p2,[],[Wand(Form(p21,s21,c21),Form(p22,s22,c22))])) (* very simple wand case *)
		   -> apply_tactic_till_fail logic failing (ts,(f,(p21@p1,s21@s1,c21@c1),(p22@p2,s22,c22)))
	   | _ ->  
		let tactic,rwm,ep = logic in
		match tactic with
			|	Rules rules -> 
				Format.printf "Rules: %i@\n" (List.length rules);
				(
					try (false, List.flatten (apply_rule_list_once rules seq ep))
 	    	  with No_match -> 
					Format.printf "   No rules match@\n";
						(true, failing seq)
				)
			| Repeat tc ->
				let (failed,seqss) = apply_tactic_till_fail (tc,rwm,ep) failing seq in
				Format.printf "Repeat: %a@\n" string_ts_seq (List.hd seqss);
				if failed then (true, seqss)
				else (false, sequents_backtrack (slim (apply_tactic_till_fail logic failing)) seqss [])
			| IfMatch (tc_if,tc_then,tc_else) ->
					Format.printf "IfMatch";
				let failing_if = apply_tactic_till_fail (tc_else,rwm,ep) failing in
				let (failed,seqss) = apply_tactic_till_fail (tc_if,rwm,ep) (slim failing_if) seq in
				(failed, sequents_backtrack (slim (apply_tactic_till_fail (tc_then,rwm,ep) failing)) seqss [])
	in
	let seqs = tidy_sequents logic seqs in
	let apply = slim (apply_tactic_till_fail logic failing) in
	List.flatten (List.map apply seqs)

(* same as apply_rule_list *)
(* but replace calls to apply_rule_list_once *)
(* with calls to apply_tactic_once *)
let rec apply_tactic logic (sequents : ts_sequent list) find_frame abs : ts_sequent list =
(* Clear pretty print buffer *)
(*  Buffer.clear buffer_dump;	*)
  let tactic,rwm,ep = logic in
  if true || !(Debug.debug_ref) then
    (List.iter (fun seq -> Format.fprintf !dump "Goal@ %a@\n@\n" string_ts_seq seq) sequents;
     Format.fprintf !dump "Start time :%f @\n" (Sys.time ()));
	let plain_rules = [] in	
  	Format.printf "Goals: %i@\n" (List.length sequents);
	let at_fail seq = match seq with  (* no more rules apply: see if we have a plain contradiction *)  
		 | ts,(f,(p1,s1,c1),(p2,s2,c2)) -> 
		     if true || !(Debug.debug_ref) then Format.fprintf !dump "Find plain contradiction:\n";
		     try apply_plain_prove_contra plain_rules ep (ts,(f,s1,c1)) p1 (* Prove plain thing *)
		     with Failed -> raise (Failed_eg [seq])
		 | _ -> raise Failed
	in
	let try_right seq =
		let seqs = apply_rule_or_right seq in
		let seqs = List.map (List.map apply_rule_flatten) seqs in 
		sequents_backtrack (lifted_apply_tactic_till_fail logic abs at_fail) seqs []
	in
	let try_left seq =
	  Format.printf "  Trying left@\n";		
		let seqs = apply_rule_or_left seq in 
		let seqs = List.map apply_rule_flatten seqs  
		in lifted_apply_tactic_till_fail logic abs try_right seqs
	in
	let check_done seq =
	  Format.printf "  Checking done@\n";
		try
			(
		match seq with  (* no more rules apply: see if we have done the proof *)  
		 | ts,(f,(p1,s1,c1),(p2,[],[])) -> 
			  Format.printf "..almost..@\n";
		     if find_frame || (s1=[] && c1=[]) then 
		       try 
			       let res = apply_plain_prove plain_rules ep (ts,(f,s1,c1)) p1 p2 in (* Prove plain thing *)
						 Format.printf "...%i@\n" (List.length res);
						 res
		       with Failed -> 
					Format.printf "..plain fail..@\n";
			 (if (c1=[]) then raise (Failed_eg [seq]) else raise No_match)
		     else 
				  (
					Format.printf "..raise stakes..@\n";
					raise No_match
					)
		 | ts,(f,(p1,s1,c1),f2) ->
			  Format.printf "..nope, ask friend..@\n";		     
		     (* ask the audience *)
	       (try 
	         let sub = ask_the_audience ep ts p1 (rv_sequent (f,(p1,s1,c1),f2)) in 
	         lifted_apply_tactic_till_fail logic abs try_left [ts, subst_sequent sub (f,(p1,s1,c1),f2)] 
	        with Contradiction -> [])
			)
		with No_match -> try_left seq
	in
	let try_rewrite seq =
	  Format.printf "  Rewriting@\n";
		let seq = rewrites_sequent rwm ep abs true seq in
		lifted_apply_tactic_till_fail logic abs check_done [seq]
	in
	let res = lifted_apply_tactic_till_fail logic abs try_rewrite sequents in
	if true || !(Debug.debug_ref) then Format.fprintf !dump "End time :%f @\n@?" (Sys.time ()); res

			
(*  Refactor for frame inference *)
let rec apply_rule_list logic (sequents : ts_sequent list) find_frame abs : ts_sequent list 
    =
(* Clear pretty print buffer *)
  Buffer.clear buffer_dump;
  let plain_rules = [] in 
  let rules,(*emps,plain_rules,*)rwm,ep = logic in 
  let n = 0 in
  if true || !(Debug.debug_ref) then
    (List.iter (fun seq -> Format.fprintf !dump "Goal@ %a@\n@\n" string_ts_seq seq) sequents;
     Format.fprintf !dump "Start time :%f @\n" (Sys.time ()));
  let rec apply_rule_list_inner sequents n : ts_sequent list = 
		let sequents = tidy_sequents logic sequents in 
	  (* Apply rules lots *)
    List.flatten 
      (List.map 
	 (fun seq -> 
	   try 
	     (* check for base sequents *)
	     if true || !(Debug.debug_ref) then Format.fprintf !dump "%s>@[%a@]@\n@." (String.make n '-') string_ts_seq  seq;
	     match seq with 
	     | ts,(f,(p1,s1,c1),(p2,[],[Wand(Form(p21,s21,c21),Form(p22,s22,c22))])) (* very simple wand case *)
		   -> apply_rule_list_inner [ts,(f,(p21@p1,s21@s1,c21@c1),(p22@p2,s22,c22))] (n+1)
	     | _ ->  
		 let seqss = apply_rule_list_once rules seq ep
		 in sequents_backtrack (fun seqs->apply_rule_list_inner seqs (n+1)) seqss []
	   with No_match -> 
	     (* Do expensive rewrites and try again *)
	     let seq = rewrites_sequent rwm ep abs true seq in 
	     try 
	       let seqss = apply_rule_list_once rules seq ep
	       in sequents_backtrack (fun seqs->apply_rule_list_inner seqs (n+1)) seqss []
	     with No_match -> 
	       try 
		 match seq with  (* no more rules apply: see if we have done the proof *)  
		 | ts,(f,(p1,s1,c1),(p2,[],[])) -> 
		     if find_frame || (s1=[] && c1=[]) then 
		       try 
			 apply_plain_prove plain_rules ep (ts,(f,s1,c1)) p1 p2 (* Prove plain thing *)
		       with Failed -> 
			 (if (c1=[]) then raise (Failed_eg [seq]) else raise No_match)
		     else raise No_match
(* TODO:  This match is disabled, should be enabled once SMT integration is complete*)
(*		 | ts,(f,(p1,s1,c1),(p2,[],c2)) ->
		     let interp = (Rhash_args.create 30) in 
		     let hash = (rao_create ()) in 
		     let rs = rv_trans_set (rv_form (p1,s1,c1) (rv_spat_list f Rset.empty)) in 
		     let x = composite_list_is_plain interp rs hash ts c2 in 
		     (match x with 
		       None -> 
			 (try 
			   let sub = ask_the_audience ep ts p1 (rv_sequent (f,(p1,s1,c1),(p2,[],c2))) in 
			   apply_rule_list_inner [ts, subst_sequent sub (f,(p1,s1,c1),(p2,[],c2))] (n+1) 
			 with Contradiction -> [])
	             | Some p_goal -> 
			 try (* If pure prover complete can raise Failed *)
			   apply_plain_prove_2 plain_rules ep (ts,(f,s1,c1)) p1 p2 p_goal c2 interp hash(* Prove plain thing *) 
			 with Failed -> raise No_match
	             )    *) 
		 | ts,(f,(p1,s1,c1),f2) ->
		     
		     (* ask the audience *)
	       (try 
	         let sub = ask_the_audience ep ts p1 (rv_sequent (f,(p1,s1,c1),f2)) in 
	         apply_rule_list_inner [ts, subst_sequent sub (f,(p1,s1,c1),f2)] (n+1) 
	        with Contradiction -> [])
		 with No_match -> 
		 try (* deal with or on left *)
		   let seqs = apply_rule_or_left seq in 
		   let seqs = List.map apply_rule_flatten seqs  
		   in apply_rule_list_inner seqs (n+1)
		 with No_match ->  (* Very niave deal with or on right *)
		   try
		     let seqs = apply_rule_or_right seq in
		     let seqs = List.map (List.map apply_rule_flatten) seqs in 
		     sequents_backtrack (fun seqs->apply_rule_list_inner seqs (n+1)) seqs []
		     (*in let rec f seqs =  back tracking is done by this function 
					    match seqs with 
					    | [] ->
		       if true || !(Debug.debug_ref) then Printf.printf "Failed to prove:\n%s > %s\n\n" (String.make n '-') (string_seq seq);
		       [seq]
		   | seq::seqs -> 
		       try 
			 (let seqs_res =  apply_rule_list_inner [seq] (n+1) in
			 if List.for_all (fun (f,(p1,s1),(p2,s2)) -> (p2=[] && s2 =[] && (s1=[] || find_frame))) seqs_res
			 then seqs_res
			 else f seqs)
		       with Failed -> f seqs
		 in f seqs *)
	       with No_match -> (
		 (* try and find plain contradiction *)
		 match seq with  (* no more rules apply: see if we have a plain contradiction *)  
		 | ts,(f,(p1,s1,c1),(p2,s2,c2)) -> 
		     if true || !(Debug.debug_ref) then Format.fprintf !dump "Find plain contradiction:\n";
		     try apply_plain_prove_contra plain_rules ep (ts,(f,s1,c1)) p1 (* Prove plain thing *)
		     with Failed -> raise (Failed_eg [seq])
		 | _ -> raise Failed)
	 ) sequents 
      )
  in let res = apply_rule_list_inner sequents n in 
  if true || !(Debug.debug_ref) then Format.fprintf !dump "End time :%f @\n@?" (Sys.time ()); res



(*let rec tidy_one (pl,sl) = 
  let neqs,other = List.partition (fun p -> match p with NEQ _ -> true | _ -> false) pl in 
  let sfv = ev_spat_list sl vs_empty in 
  let evs = ev_plain_list other sfv in 
  (List.filter 
    (fun neq -> 
      match neq with 
	NEQ(Arg_var var,_) 
      | NEQ(_,Arg_var var) -> 
	  (match var with 
	  | EVar _ -> vs_mem var evs 
	  | _ -> true)
      | EQ(x,y) -> not(x=y)
      | _ -> true )
    neqs) @ other, sl
*)  
let tidy x = (*List.map tidy_one*) x


let rec get_frames (seqs : ts_sequent list) 
    =  
  match seqs with
    [] -> []
  | seq :: seqs ->
      (match seq with
	ts,(frame,(p1,s1,c1),([],[],[])) -> 
	  [ts,(p1,s1,c1)] @ (get_frames seqs)
      | _ -> raise Failed)

let rec get_frames2 (seqs : ts_sequent list) 
    =  
  match seqs with
    [] -> []
  | seq :: seqs ->
      (match seq with
	(ts,(frame,(p1,s1,c1),([],[],[]))) -> 
	  [ts,(p1,s1,c1)] @ (get_frames seqs)
      | _ -> raise Failed)


(* returns formula for the possible frames:
   empty list, implies heap1 is inconsistent
 *)
let check_implication_frame_inner logic ts heap1 heap2 =
  try
     let frames = get_frames (apply_tactic logic [ts,([],heap1,heap2)] true false) in
     frames
  with 
    Failed -> [] 
  | Failed_eg x -> prover_counter_example := x; []

let check_implication_frame logic (ts1,heap1) (ts2,heap2)  =
  (* Do some kind of merge of ts2 and ts1 *)
  let eqs,subst = ts_to_eqs ts2 ts1 (rv_form heap2 Rset.empty) in 
  let pl,sl,cl = (subst_form subst heap2) in
  let pl = (List.map (fun (x,y) -> EQ(x,y)) eqs) @ pl in 
  check_implication_frame_inner logic ts1 heap1 (pl,sl,cl)

let check_implication_frame_pform logic (ts1,heap1) pheap  =
  let heap2,subst = pform_convert ts1 Rterm.empty_vs pheap true in
  check_implication_frame_inner logic ts1 heap1 heap2


let abs logic (ts,heap1)  =
  try
    let seqs = 	[ts,([],heap1,([],[],[]))] in 
    get_frames2 (apply_tactic logic seqs true true) 
  with Failed -> []
  | Failed_eg x-> prover_counter_example := x;  []

let check_implication_inner logic ts heap1 heap2 =
(*  let subs = Logic.concrete_subs() in 
  let heap1 = subst_form subs heap1 in *)
  try
    ignore (get_frames (apply_tactic logic [ts,([],heap1,heap2)] false false)); true
  with Failed -> false
  | Failed_eg x -> prover_counter_example := x ; false


let check_implication logic (ts1,heap1) (ts2,heap2)  =
  (* Do some kind of merge of ts2 and ts1 *)
  let eqs,subst = ts_to_eqs ts2 ts1 (rv_form heap2 Rset.empty) in 
  let pl,sl,cl = try (subst_form subst heap2) with Contradiction -> ([],[],[False]) in
  let pl = (List.map (fun (x,y) -> EQ(x,y)) eqs) @ pl in 
  check_implication_inner logic ts1 heap1 (pl,sl,cl)



let check_inconsistency logic ((ts,heap1) : ts_form)  = 
  check_implication_inner logic ts heap1 ([],[],[False]) 


(* This is inefficient, but save writing a new interface *)
let check_equal logic (f : ts_form) (a1 : args) (a2 : args)  = 
    match check_implication_frame logic f (Rlogic.convert (mkEQ(a1,a2))) with
      [] -> false
    | _ -> true


let check_equiv (f1 : ts_form) (f2 : ts_form) =
  check_implication empty_logic f1 f2 && check_implication empty_logic f2 f1


let check_equiv (fl1 : ts_form list) (fl2 : ts_form list) =
  let lifted_imp fl1 fl2 = 
    List.for_all 
      (fun f1 -> 
	List.exists
	  (fun f2 -> 
	    check_implication empty_logic f1 f2
	  ) fl2
      ) fl1 in
  lifted_imp fl1 fl2 && lifted_imp fl2 fl1


     
(* 
let interpret_exist_in_form ((plain,spat,combined) : form) (ev : var) =
  (match ev with
    EVar _ -> ()
  | _ -> unsupported ())
	;
  match subst_eqs plain with 
    None-> None
  | Some (_,subs,_) ->
      (
      let rarg = subst_var subs ev in
      match rarg with
	Arg_var v -> if v=ev then None else Some rarg
      |  _ -> Some rarg
      )
*)
