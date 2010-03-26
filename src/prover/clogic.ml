(********************************************************
   This file is part of jStar 
	src/prover/clogic.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)
open Congruence
open Misc
open Cterm
open Multiset
open Backtrack 
open Psyntax

exception Success
exception Failed

module RMSet = MultisetImpl(
  struct
    type t = string * Cterm.representative
    let compare (s1,r1) (s2,r2) = 
      if s1 < s2 then 
	-1
      else if s1 = s2 then
	compare r1 r2 
      else 
	1
  end
)

type multiset = RMSet.multiset

module SMSet = MultisetImpl(
  struct
    type t = string * (Psyntax.args list)
    let compare (s1,r1) (s2,r2) = 
      if s1 < s2 then 
	-1
      else if s1 = s2 then
	compare r1 r2 
      else 
	1
  end
)



type syntactic_form = 
  {
   sspat : SMSet.multiset;
   splain : SMSet.multiset;
   sdisjuncts : (syntactic_form * syntactic_form) list;
   seqs : (Psyntax.args * Psyntax.args) list;
   sneqs : (Psyntax.args * Psyntax.args) list;
 }


type formula =
    {
    spat : RMSet.multiset;
    plain : RMSet.multiset;
    disjuncts : (formula * formula) list;
    eqs : (representative * representative) list;
    neqs : (representative * representative) list; 
  }  

type ts_formula = 
    {
    ts : Cterm.term_structure;
    form : formula;
    cache_sform : syntactic_form option ref;
  } 

let mk_ts_form ts form =
  {ts = ts; form = form; cache_sform = ref None}

let break_ts_form ts_form = 
  ts_form.ts, ts_form.form

let kill_var ts_form v = 
  {ts_form with ts = Cterm.kill_var ts_form.ts v}

let update_var_to ts_form v e = 
  {ts_form with ts = Cterm.update_var_to ts_form.ts v e}

let pp_rmset_pre pre ts ppf s = 
  let rec f s = 
    if RMSet.has_more s then 
      let (n,x),s = RMSet.remove s in 
      Format.fprintf ppf "@[%s%s%a@]" pre n (pp_c ts) x;
      if RMSet.has_more s then 
	begin Format.fprintf ppf "@ *@ "; f s end
  in f s

let pp_rmset ts ppf s = 
  pp_rmset_pre "" ts ppf s 

let rec pp_form ts ppf form = 
  List.iter
    (fun (r1,r2) -> 
      Format.fprintf ppf "@[%a=%a@]@ *@ " (pp_c ts) r1 (pp_c ts) r2)
    form.eqs;
  List.iter
    (fun (r1,r2) -> 
      Format.fprintf ppf "@[%a!=%a@]@ *@ " (pp_c ts) r1 (pp_c ts) r2)
    form.neqs;

  (* Print spatial *)  
  pp_rmset ts ppf form.spat; 
  (* Print plain *)
  pp_rmset_pre "!" ts ppf form.plain; 
  (* Print disjuncts *)
  List.iter 
    (fun (d1,d2) -> 
      Format.fprintf ppf "*@ @[(@[%a@]@ ||@ @[%a@])@]" (pp_form ts) d1 (pp_form ts) d2
  )
    form.disjuncts


let pp_smset_pre pre ppf s = 
  let rec f s = 
    if SMSet.has_more s then 
      let (n,x),s = SMSet.remove s in 
      Format.fprintf ppf "@[%s%s(%a)@]" pre n string_args_list x;
      if SMSet.has_more s then 
	begin Format.fprintf ppf "@ *@ "; f s end
  in f s

let pp_smset ppf s = 
  pp_smset_pre "" ppf s 

let rec pp_sform ppf form = 
  List.iter
    (fun (r1,r2) -> 
      Format.fprintf ppf "@[%a=%a@]@ *@ " string_args r1 string_args r2)
    form.seqs;
  List.iter
    (fun (r1,r2) -> 
      Format.fprintf ppf "@[%a!=%a@]@ *@ " string_args r1 string_args r2)
    form.sneqs;

  (* Print spatial *)  
  pp_smset ppf form.sspat; 
  (* Print plain *)
  pp_smset_pre "!" ppf form.splain; 
  (* Print disjuncts *)
  List.iter 
    (fun (d1,d2) -> 
      Format.fprintf ppf "*@ @[(@[%a@]@ ||@ @[%a@])@]" pp_sform d1 pp_sform d2
  )
    form.sdisjuncts


let pp_ts_form ppf ts_form =
  let ts = ts_form.ts in 
  (* Print term_structure *)
  Cterm.pp_ts ppf ts;
  (* Print eqs and neqs *)  
  pp_form ts ppf ts_form.form

let conjunction form1 form2 : formula=
  {
  spat = RMSet.union form1.spat form2.spat;
  plain = RMSet.union form1.plain form2.plain;
  disjuncts = form1.disjuncts @ form2.disjuncts;
  eqs = form1.eqs @ form2.eqs;
  neqs = form1.neqs @ form2.neqs;				 
}   

let disjunction form1 form2 : formula = 
  { 
  spat = RMSet.empty;
  plain = RMSet.empty;
  disjuncts = [(form1,form2)];
  eqs =[];
  neqs = [];
} 

let empty : formula = 
  {
  spat = RMSet.empty;
  plain = RMSet.empty;
  disjuncts = [];
  eqs = [];
  neqs = [];
} 

let false_sform = 
  {
  sspat = SMSet.empty;
  splain = SMSet.lift_list [("@False",[])];
  sdisjuncts = [];
  seqs = [];
  sneqs = [];
} 

let is_sempty s = 
  s.sspat = SMSet.empty &&
  s.splain = SMSet.empty &&
  s.sdisjuncts = [] &&
  s.seqs = [] &&
  s.sneqs = [] 

let truth = empty

let is_true form = 
  form.spat = RMSet.empty
    && form.plain = RMSet.empty
    && form.disjuncts = []
    && form.eqs = []
    && form.neqs = []


let add_eqs_t_list fresh eqs ts : term_structure =
  List.fold_left (fun ts (x,y) -> 
    try 
      make_equal_t fresh ts x y
    with Contradiction -> 
      Format.fprintf !(Debug.dump) "Trying to make %a and %a equal failed" string_args x string_args y; 
      raise Contradiction 
      ) ts eqs

let add_neqs_t_list fresh neqs ts : term_structure = 
  List.fold_left (fun ts (x,y) -> 
    try 
      make_not_equal_t fresh ts x y
    with Contradiction -> 
      Format.fprintf !(Debug.dump) "Trying to make %a and %a not equal failed" string_args x string_args y; 
      raise Contradiction 
      ) ts neqs

let add_eqs_list eqs ts : term_structure =
  List.fold_left (fun ts (x,y) -> make_equal ts x y) ts eqs

let add_neqs_list neqs ts : term_structure = 
  List.fold_left (fun ts (x,y) -> make_not_equal ts x y) ts neqs


  (* As multiple representatives might be equal, 
     we have to use a comparison based only on the predicate name.  
     The sorting means predicates with the same name will be next 
     to each other. *)
let intersect_with_ts ts rem_snd set1 set2 =  
  let loose_compare a b = compare (fst a) (fst b) in 
  let equal (an,ar) (bn,br) = an=bn && equal ts ar br in 
  let rec match_same rem_snd set1 set2 intersect count = 
    if RMSet.has_more set1 && RMSet.has_more set2 then 
      let c1,nset1 = RMSet.remove set1 in
      let c2,nset2 = RMSet.remove set2 in	  
      if loose_compare c1 c2 = 0 then 
	if equal c1 c2 then 
	  let nset2 = (if rem_snd then nset2 else set2) in 
	  match_same rem_snd nset1 (RMSet.back nset2 count) (c2::intersect) 0	      	      
	else
	    (* Not a match, try next. *)
	  match_same rem_snd set1 (RMSet.next set2) intersect (count+1)
      else if loose_compare c1 c2 < 0 then 
	  (* First set is a low one, so skip element,
	     reverse second set over similar elements incase next element is same class*)
	match_same rem_snd (RMSet.next set1) (RMSet.back set2 count) intersect 0
      else 
	  (* Second set has lowest element, so skip element *)
	match_same rem_snd set1 (RMSet.next set2) intersect 0
    else
	(* No more left to match *)
      (RMSet.lift_list intersect, RMSet.restart set1, RMSet.restart set2) 
  in
  match_same rem_snd set1 set2 [] 0



let rec normalise ts form : formula * term_structure = 
(*  Format.printf "Normalising formula : %a @\n" pp_ts_form  {ts=ts;form=form};*)
  let rec f nform ts disj =
    match disj with 
      [] -> nform,ts
    | (f1,f2)::disj ->
	let f1o = 
	  try 
	    let ts1 = add_eqs_list f1.eqs ts in
	    let ts1 = add_neqs_list f1.neqs ts1 in
	    let f1,ts1 = normalise ts1 f1 in 	  
	    Some (f1,ts1)
	  with Contradiction -> 
(*	    Format.printf "Contradiction left@\n";*)
	    None in 
	let f2o =
	  try
	    let ts2 = add_eqs_list f2.eqs ts in 
	    let ts2 = add_neqs_list f2.neqs ts2 in
	    let f2,ts2 = normalise ts2 f2 in 
	    Some (f2,ts2)
	  with Contradiction ->
(*	    Format.printf "Contradiction right@\n";*)
	    None in 
	match f1o,f2o with 
	  None,None -> raise Contradiction
	| Some (form,ts'), None
	| None, Some (form,ts') ->
	    Format.fprintf !(Debug.dump) "Disjunct eliminated! Remaining disjunct:@ %a@\n" (pp_form ts) form ;
	    let nform = (conjunction form nform) in 
	    f nform
	      ts'
	      disj
	| Some (f1,_),Some (f2,_) -> 
	    (* TODO intersect is too discriminating *)
	    let s,s1,s2 = intersect_with_ts ts true f1.spat f2.spat in 
	    let p,p1,p2 = intersect_with_ts ts true f1.plain f2.plain in
	    let f1 = {f1 with spat=s1;plain=p1} in 
	    let f2 = {f2 with spat=s2;plain=p2} in 	    
	    f 
	      {nform with 
	       spat = RMSet.union s nform.spat;
	       plain = RMSet.union p nform.plain;
	       disjuncts =
	       if is_true(f1) || is_true(f2) then 
		 nform.disjuncts
	       else
		 ((f1,f2)::nform.disjuncts)
	     }
	      ts
	      disj
  in
  let form,ts = f {form with disjuncts=[]} ts form.disjuncts in 
(*  Format.printf "Normalised formula : %a @\n" pp_ts_form  {ts=ts;form=form};*)
  form,ts

let rec out_normalise ts form =
  let form,ts = normalise ts form in
  if form.eqs != [] || form.neqs != [] then
    begin 
      let ts = add_eqs_list form.eqs ts in 
      let ts = add_neqs_list form.neqs ts in 
      let form,ts = out_normalise ts {form with eqs = []; neqs = []} in 
      form,ts
    end
  else
    form,ts




let rec convert_to_inner (form : Psyntax.pform) : syntactic_form = 
  let convert_atomic_to_inner (sspat,splain,sdisj,seqs,sneqs) pat = 
    match pat with 
      P_EQ (a1,a2) -> sspat, splain,sdisj,(a1,a2)::seqs, sneqs
    | P_NEQ (a1,a2) -> sspat, splain,sdisj,seqs, (a1,a2)::sneqs
    | P_PPred (name, al) -> sspat, ((name, al)::splain),sdisj,seqs,sneqs
    | P_SPred (name, al) -> ((name,al)::sspat), splain,sdisj,seqs,sneqs
    | P_Wand _ | P_Septract _
    | P_Garbage -> ("@Garbage",[])::sspat, splain,sdisj,seqs,sneqs
    | P_False -> sspat, (("@False", [])::splain),sdisj,seqs,sneqs
    | P_Or(f1,f2) ->
	let f1 = convert_to_inner f1 in 
	let f2 = convert_to_inner f2 in 
	sspat, splain, (f1,f2)::sdisj, seqs, sneqs
  in 
  let (sspat,splain,sdisj,seqs,sneqs) = List.fold_left convert_atomic_to_inner ([],[],[],[],[]) form in
  {
   sspat = SMSet.lift_list sspat;
   splain = SMSet.lift_list splain;
   sdisjuncts = sdisj;
   seqs = seqs;
   sneqs = sneqs;
 }

let smset_to_list fresh a ts = 
  let a = SMSet.restart a in
  let rec inner a rs ts = 
    if SMSet.has_more a then
      let (n,tl),a = SMSet.remove a in
      let c,ts = add_tuple fresh tl ts in
      inner a ((n,c)::rs) ts
    else
      rs, ts
  in inner a [] ts 
let rec add_pair_list fresh xs ts rs = 
  match xs with 
    [] -> rs,ts
  | (a,b) ::xs -> 
      let c1,ts = add_term fresh a ts in 
      let c2,ts = add_term fresh b ts in 
      add_pair_list fresh xs ts ((c1,c2)::rs)
(* Will convert eqs into ts for or which is wrong. *)
let rec convert fresh (ts :term_structure) (sf : syntactic_form) : formula * term_structure =
  let spat, ts = smset_to_list fresh sf.sspat ts in 
  let plain, ts = smset_to_list fresh sf.splain ts in 
  let disj, ts  = convert_sf_pair_list fresh ts sf.sdisjuncts [] in
  let ts = add_eqs_t_list fresh sf.seqs ts in 
  let ts = add_neqs_t_list fresh sf.sneqs ts in 
  {spat = RMSet.lift_list spat; plain = RMSet.lift_list plain; disjuncts = disj;eqs=[];neqs=[]}, ts
and convert_without_eqs 
 fresh (ts :term_structure) (sf : syntactic_form) : formula * term_structure =
  let spat, ts = smset_to_list fresh sf.sspat ts in 
  let plain, ts = smset_to_list fresh sf.splain ts in 
  let disj, ts  = convert_sf_pair_list fresh ts sf.sdisjuncts [] in
  let eqs,ts = add_pair_list fresh sf.seqs ts [] in 
  let neqs,ts = add_pair_list fresh sf.sneqs ts [] in 
  {spat = RMSet.lift_list spat; plain = RMSet.lift_list plain; disjuncts = disj;
  eqs=eqs;neqs=neqs}, ts

and convert_sf_pair_list 
    fresh (ts :term_structure) 
    (sf : (syntactic_form * syntactic_form) list) 
    (rs : (formula * formula) list) 
  : ((formula * formula) list) * term_structure =
  match sf with 
    [] -> rs,ts
  | (x,y)::sf -> 
      let x,ts = convert_without_eqs fresh ts x in
      let y,ts = convert_without_eqs fresh ts y in
      convert_sf_pair_list fresh ts sf ((x,y)::rs)

let conjoin fresh (f : ts_formula) (sf : syntactic_form) = 
  let nf,ts = convert fresh f.ts sf in 
  let nf = conjunction nf f.form in 
  {ts = ts; form = nf; cache_sform = ref None}





let match_and_remove 
      remove (* should match terms be removed: true removes them, false leaves them*) 
      ts 
      term (*formula to match in *)
      pattern (*pattern to match *)
      cont 
    =
  let rec mar_inner
	ts 
	(term : RMSet.multiset)
	(cn (*current name*),cp (*current tuple pattern*)) 
	pattern(*remaining pattern*) 
	count (*number of successive failures to match *) 
	(cont : term_structure * RMSet.multiset -> 'a) : 'a = 
      if RMSet.has_more term then 
	(* actually do something *)
	let s,nterm = RMSet.remove term in
	if fst(s) = cn then 
	  (* potential match *)
	  try 
	    unifies ts cp (snd(s))
	      (fun ts ->
               (* If we are removing matched elements use nterm, otherwise revert to term *)
		let nterm = if remove then nterm else term in 
		if SMSet.has_more pattern then 
		  (* match next entry in the pattern*)	   
		  let ((nn,np), pattern) = SMSet.remove pattern in
		  (* If we are matching the same type of predicate still, 
		     then must back the iterator up across the failed matches.  *)
		  let nterm = if nn=cn then (RMSet.back nterm count) else nterm in 
		  let np,ts = make_tuple_pattern np ts in 
		  mar_inner
		    ts 
		    nterm
		    (nn, np)
		    pattern
		    0
		    cont
		else
                  (* No pattern left, done *)
		  cont (ts,RMSet.restart nterm) 	  
	      )
	  with Backtrack.No_match ->
	    (* Failed to match *)
	    mar_inner ts (RMSet.next term) (cn,cp) pattern (count+1) cont
	else if fst(s) < cn then
	  (* keeping searching for a new predicate, as current is too low. *)
	  mar_inner ts (RMSet.next term) (cn,cp) pattern 0 cont
	else
	  (* We have missed it, so no match *)
	  raise No_match
      else
	(* pattern left, but nothing to match against *)
	raise No_match
  in 
    (* Check the pattern is non-empty *)
    if SMSet.has_more pattern then 
      let (cn,cp),pattern = SMSet.remove pattern in 
      let cp,ts = make_tuple_pattern cp ts in     
      mar_inner ts term (cn,cp) pattern 0 cont 
    else 
      (* Empty pattern just call continuation *)
      cont (ts,term)
	
	

(* Assume that assumption does not contain eqs or neqs, they are represented in ts *)
type sequent =
   {
    matched : RMSet.multiset;
    ts : term_structure;
    assumption : formula;
    obligation : formula;      
  } 
  
let empty_sequent () = 
  {
  matched = RMSet.empty;
  ts = Cterm.new_ts ();
  assumption = empty;
  obligation = empty;
} 

let pp_sequent ppf seq = 
  Format.fprintf ppf 
    "@[%a@]@ |@ @[%a%a@]@ |-@ @[%a@]"  
    (pp_rmset seq.ts) seq.matched
    pp_ts seq.ts
    (pp_form seq.ts) seq.assumption
    (pp_form seq.ts) seq.obligation

    

let rec plain f =
  f.spat = RMSet.empty
    &&
  List.for_all (fun (x,y) -> plain x && plain y) f.disjuncts

let true_sequent (seq : sequent) : bool = 
  (is_true seq.obligation)
    &&
  plain seq.assumption

let frame_sequent (seq : sequent) : bool = 
  (seq.obligation = empty) 


(* Stolen from Prover just for refactor *)
type sequent_rule = psequent * (psequent list list) * string * ((* without *) pform * pform) * (where list)


type pat_sequent =
    {
    assumption_same : syntactic_form;
    assumption_diff : syntactic_form;
    obligation_diff : syntactic_form;
  }
      
let convert_sequent (ps : psequent) : pat_sequent =
(*  Format.fprintf !(Debug.dump) "Converting sequent: %a@\n" string_pseq ps;*)
  let ps = match ps with
    pm,pa,po -> 
      {
       assumption_same = convert_to_inner pm;
       assumption_diff = convert_to_inner pa;
       obligation_diff = convert_to_inner po;
     } in 
(*  Format.fprintf !(Debug.dump) "Produced sequent: %a@ |@ %a@ |-@ %a@\n@\n" pp_sform ps.assumption_same pp_sform ps.assumption_diff pp_sform ps.obligation_diff; *)
  ps

type inner_sequent_rule =
    {
      conclusion : pat_sequent ;
      premises : pat_sequent list list;
      name : string;
      without_left : syntactic_form;
      without_right : syntactic_form;
      where : where list;
   }


let convert_rule (sr : sequent_rule) : inner_sequent_rule = 
  match sr with 
    conc,prems,name,(withoutl,withoutr),where ->
      {
       conclusion = convert_sequent conc;
       premises = List.map (List.map convert_sequent) prems;
       name = name;
       without_left = convert_to_inner withoutl;
       without_right = convert_to_inner withoutr;
       where = where;       
     }


let sequent_join fresh (seq : sequent) (pseq : pat_sequent) : sequent option = 
  try 
    let ass,ts = 
      try 
	convert fresh  seq.ts pseq.assumption_diff 
      with Contradiction -> 
	Format.fprintf !(Debug.dump) "Failed to add formula to lhs: %a@\n" pp_sform pseq.assumption_diff;
	raise Contradiction
    in
    let ass = conjunction ass seq.assumption in
    let sam,ts = 
      try 
	convert fresh ts pseq.assumption_same 
      with Contradiction ->
	Format.fprintf !(Debug.dump) "Failed to add formula to matched: %a@\n" pp_sform pseq.assumption_same;
	assert false in 
    let sam = RMSet.union sam.spat seq.matched in 
    let obs,ts = 
      try 
	let obs,ts = convert_without_eqs fresh ts pseq.obligation_diff in
	let obs = conjunction obs seq.obligation in 
	obs,ts
      with Contradiction ->
	try 
	  convert_without_eqs true ts false_sform
	with Contradiction -> assert false
    in 
    Some {
     assumption = ass;
     obligation = obs;
     matched = sam;
     ts = ts;
   }
  with Contradiction -> 
    Format.fprintf !(Debug.dump) "Contradiction detected!!@\n";
    None

let sequent_join_fresh = sequent_join true
let sequent_join = sequent_join false

let make_sequent (pseq : pat_sequent) : sequent option = 
  sequent_join (empty_sequent ()) pseq

(* Match in syntactic ones too *)
let rec match_foo op ts form seqs cont = 
  match seqs with 
    [] -> cont (ts,form) 
  | (x,y)::seqs ->
      let x,ts = add_pattern x ts in 
      let y,ts = add_pattern y ts in 
      try
	op ts x y (fun ts -> match_foo op ts form seqs cont)
      with No_match -> 
	let rec f ts frms frms2=
	  match frms with 
	    (a,b)::frms -> 
	      begin 
		try 
		  unifies ts x a 
		    (fun ts -> unifies ts y b 
			(fun ts -> match_foo op ts (frms@frms2) seqs cont) )
		with No_match -> try
		  unifies ts x b 
		    (fun ts -> unifies ts y a 
			(fun ts -> match_foo op ts (frms@frms2) seqs cont) )
		with No_match ->
		  f ts frms ((a,b)::frms2)
	      end
	  | [] -> raise No_match
	in 
	f ts form []


let match_eqs ts eqs seqs cont = 
  match_foo unify_patterns ts eqs seqs cont

let match_neqs ts neqs sneqs cont = 
  match_foo unify_not_equal_pattern ts neqs sneqs cont

    

(* TODO: Currently ignores disjuncts in matching *)
let rec match_form remove ts form pat (cont : term_structure * formula -> 'a) : 'a =
  match_and_remove remove ts form.spat pat.sspat
    (fun (ts,nspat) ->
      match_and_remove remove ts form.plain pat.splain
	(fun (ts,nplain) ->
	  match_eqs ts form.eqs pat.seqs
	    (fun (ts,eqs) -> 
	      match_neqs ts form.neqs pat.sneqs 
		(fun (ts,neqs) -> 
		  match_disjunct remove ts {form with 
			      spat = nspat;
			      plain = nplain;
			      eqs = eqs;
			      neqs = neqs;
			    }
		    pat.sdisjuncts cont
		)
	    )
	)
    )
and match_disjunct remove ts form pat_disj cont =
  match pat_disj with 
    [] -> cont (ts,form)
  | (x,y)::pat_disj -> 
      try 
	match_form remove ts form x (fun (ts,form) -> match_disjunct remove ts form pat_disj cont)
      with No_match -> 
	match_form remove ts form y (fun (ts,form) -> match_disjunct remove ts form pat_disj cont)

let contains ts form pat : bool  = 
  try 
    match_form true ts form pat (fun (ts2,_) -> if Cterm.ts_eq ts ts2 (*This checks that no unification has occured in the contains*) then true else  raise Backtrack.No_match)
  with No_match -> 
    false


let rec form_reps form reps =
  let reps = (RMSet.map_to_list form.spat snd) @ reps in 
  let reps = (RMSet.map_to_list form.plain snd)  @ reps in 
  let reps = List.fold_left (fun acc (a,b) -> a::b::acc) reps form.eqs in
  let reps = List.fold_left (fun acc (a,b) -> a::b::acc) reps form.neqs in
  let reps = List.fold_left (fun acc (a,b) -> form_reps a (form_reps b acc)) reps form.disjuncts in
  reps 

let rec sequent_reps sequent reps =
  let reps = (RMSet.map_to_list sequent.matched snd) @ reps in 
  let reps = form_reps sequent.assumption reps in 
  let reps = form_reps sequent.obligation reps in 
  reps




let rewrite_guard_check seq (ts,guard) =
  if contains ts seq.assumption (convert_to_inner guard.if_form) then
    let without = convert_to_inner guard.without_form in 
    if not (is_sempty without) && contains ts seq.assumption without then 
      false
    else 
      (* TODO add where clause *)
      true
  else
    false
      
    
let simplify_sequent rm seq : sequent option 
    =
try
(*  Format.printf "Before simplification : %a@\n" pp_sequent seq ;*)
  (* Try to prove each equality and inequality using ts.
   Note we assume ones we can prove to prove the rest.*)
  let remove test update = 
    let rec remove_rec rem_eqs ts eqs =
      match eqs with 
	[] -> rem_eqs,ts
      | (x,y)::eqs -> 
	  if test ts x y then
	    remove_rec rem_eqs ts eqs 
	  else
	    begin
	      let ts = update ts x y in 
	      remove_rec ((x,y)::rem_eqs) ts eqs 
	    end
    in remove_rec []
  in
  let ass = seq.assumption in 
  let obs = seq.obligation in 
  let ass,ts = 
    try 
      out_normalise seq.ts ass
    with Contradiction -> 
      Format.fprintf !(Debug.dump)"Success: %a@\n" pp_sequent seq;  
      raise Success
  in 
  try 
    let obs,_ = 
      try normalise ts obs
      with Contradiction -> 
	raise Failed in 
    let ob_eqs = obs.eqs in
    let rec duts ts ob_eqs new_ob_eqs = 
      match ob_eqs with 
	[] -> ts,  new_ob_eqs
      | (a,b)::ob_eqs -> 
	  let ts,obeq = determined_exists ts a b in 
	  duts ts ob_eqs (obeq @ new_ob_eqs) in
    let ts, ob_eqs = try duts ts ob_eqs [] with Contradiction -> raise Failed in   
    let ob_neqs = obs.neqs in
    let ts = try Cterm.rewrite ts rm (rewrite_guard_check seq) with Contradiction -> raise Success in 
    let ob_eqs,ts_ob = try remove equal make_equal ts ob_eqs with Contradiction -> raise Failed in 
    let ob_neqs,ts_ob = try remove not_equal make_not_equal ts_ob ob_neqs with Contradiction -> raise Failed in 
  (* Assuming obligations equalities and inequalities,
     and try to match same terms on each side *)
    let a_spat = ass.spat in 
    let o_spat = obs.spat in 
  (* Look for all the o_spat terms in a_spat,
     shared terms will be f_spat
  *)
    let (f_spat,o_spat,a_spat) = intersect_with_ts ts_ob true o_spat a_spat in 
    let f_spat = RMSet.union seq.matched f_spat in 
    let a_plain = ass.plain in 
    let o_plain = obs.plain in 
    let (_,o_plain,_) = intersect_with_ts ts_ob false o_plain a_plain in 
    let ts = try Cterm.rewrite ts rm (rewrite_guard_check seq) with Contradiction -> raise Success in 
    let seq = {
      ts = ts;
      matched = f_spat;
      assumption = {ass with spat = a_spat};
      obligation = 
      {obs with 
	spat = o_spat;
	plain = o_plain;
	eqs = ob_eqs; 
	neqs=ob_neqs
      } 
    } in
   (*  Format.printf "After simplification : %a@\n" pp_sequent seq; *)
    Some seq
  with Failed -> 
    let obs,ts = convert_without_eqs true ts false_sform in
    Some {seq with
      ts = ts;
      assumption = ass;
      obligation = obs }
	
with Success -> None


let check wheres seq = 
  let sreps = sequent_reps seq [] in 
(*  Printf.printf "list.length(sreps)=%i" (List.length sreps);*)
  List.for_all
    (
  function
    | NotInContext (Psyntax.Var varset) -> 
(*	Printf.printf "HHHHH";*)
	vs_for_all (
	  fun v -> 
	    Cterm.var_not_used_in seq.ts v sreps
	) varset
    | NotInTerm (Psyntax.Var varset, term) -> 
	assert false 
  ) wheres


(* TODO ignores where clauses in rules,
   Doesn't use obligation equalities to help with match. 
   *)
let apply_rule (sr : inner_sequent_rule) (seq : sequent) : sequent list list = 
  (* Should reset any matching variables in the ts to avoid clashes. *)
  let ts = blank_pattern_vars seq.ts in 
  (* Match obligation *)
  match_form true ts seq.obligation sr.conclusion.obligation_diff
    (fun (ts,ob) ->
      (* Match assumption_diff *)
      match_form true ts seq.assumption sr.conclusion.assumption_diff
	(fun (ts,ass) -> 
	  (* match assumption_not removed *)
	  let ass_f = {ass with spat=RMSet.union ass.spat seq.matched} in 
	  match_form true ts ass_f sr.conclusion.assumption_same
	    (fun (ts,_) ->
(*	      
   Format.fprintf !(Debug.dump) "Match rule upto contains %s@\n%a" sr.name pp_sequent
   {seq with 
   ts = ts;
   obligation = ob;
   assumption = ass;};*)
	      if (not (is_sempty sr.without_left) && contains ts ass_f sr.without_left) then 
		raise No_match
	      else if (not (is_sempty sr.without_right) && contains ts ob sr.without_right) then
		raise No_match
	      else if (not (check sr.where {seq with 
					    ts = ts; 
					    obligation = ob;
					    assumption = ass})) then
		  raise No_match
	      else begin
		Format.fprintf !(Debug.dump) "Match rule %s@\n" sr.name;
		let seq = 			    
		  {seq with 
		   ts = ts;
		   obligation = ob;
		   assumption = ass;} in 
		List.map
		  (map_option
		     (sequent_join_fresh seq))
		  sr.premises
	      end
	    )
	)
    )

(* Takes a formula, and returns a pair of formula with one of the
   original disjuncts eliminated.*)
let split_disjunct form = 
  match form.disjuncts with
    [] -> raise No_match 
  | (x,y)::disjuncts -> 
      conjunction x {form with disjuncts = disjuncts},
      conjunction y {form with disjuncts = disjuncts}

let apply_or_left seq : sequent list =
  let a1,a2 = split_disjunct seq.assumption in 
  [{seq with assumption = a1};
   {seq with assumption = a2}]

let apply_or_right seq : sequent list list =
  let o1,o2 = split_disjunct seq.obligation in 
  [[{seq with obligation = o1}];
   [{seq with obligation = o2}]]


let get_frame seq =
  assert (frame_sequent seq);
  mk_ts_form seq.ts seq.assumption

let rec get_frames seqs frms = 
  match seqs with 
    [] -> frms
  | seq::seqs ->  get_frames seqs ((get_frame seq)::frms)

let get_frames seqs = 
  get_frames seqs []


let convert_with_eqs fresh pform = 
  let sf = convert_to_inner pform in 
  let ts = new_ts () in 
  let ts,form = convert fresh ts sf in 
  mk_ts_form form ts

let convert fresh ts pform = 
  convert_without_eqs fresh  ts (convert_to_inner pform)

let make_implies heap pheap = 
  let ts,form = break_ts_form heap in 
  let rh,ts = convert false ts pheap in  
  {ts = ts;
     assumption = form;
     obligation = rh;
     matched = RMSet.empty}

let make_syntactic ts_form = 
  let ts,form = break_ts_form ts_form in 
  let eqs = get_eqs ts in 
  let neqs = get_neqs ts in 

  let rec form_to_syntax form = 
    let convert_tuple r =  
      match get_term ts r with
	Psyntax.Arg_op("tuple",al) -> al
      | _ -> assert false in 
    let convert_pair = lift_pair (get_term ts) in 
    let eqs = List.map convert_pair form.eqs in 
    let neqs = List.map convert_pair form.neqs in 
    let sspat_list = RMSet.map_to_list form.spat (fun (name,i)->(name,convert_tuple i)) in 
    let splain_list = RMSet.map_to_list form.plain (fun (name,i)->(name,convert_tuple i)) in 
    let disjuncts = List.map (lift_pair form_to_syntax) form.disjuncts in 
    {seqs= eqs;
      sneqs=neqs;
      sspat = SMSet.lift_list sspat_list;
      splain = SMSet.lift_list splain_list;
      sdisjuncts = disjuncts}
  in  
  let sform = form_to_syntax form in
  {sform with 
    seqs = sform.seqs @ eqs;
    sneqs = sform.sneqs @ neqs}


let make_implies_inner ts_form1 ts_form2 = 
  let ts,form = break_ts_form ts_form1 in
  let sform = 
    match !(ts_form2.cache_sform) with 
      Some sform -> sform 
    | None -> make_syntactic ts_form2 in
  ts_form2.cache_sform := Some sform;
  let rform,ts =  convert_without_eqs false ts sform in 
  {ts = ts;
    assumption = form;
    obligation = rform;
    matched = RMSet.empty}

