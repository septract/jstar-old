(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2009                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options

let ale = Hstring.make "<=" 
let alt = Hstring.make "<"

let is_le n = Hstring.compare n ale = 0
let is_lt n = Hstring.compare n alt = 0

module T = Term
module S = Symbols
module A = Literal
module SA = A.Set
module SAEq = A.SetEq

exception NotConsistent of SA.t

module Rat = struct
  open Num
  type t = num
      
  let of_int = num_of_string
  let of_rat = num_of_string
  let zero = Int 0
  let one = Int 1
  let minusone = Int (-1)
  let plus = add_num
  let minus = sub_num
  let mult = mult_num
  let opp_inverse x = div_num minusone x
  let div = div_num
  let abs = abs_num
  let compare = compare_num
  let print fmt x = fprintf fmt "%s" (string_of_num x)
end

type rat = Rat.t
  
module type ALIEN = sig
  type r
  val compare : r -> r -> int
  val make : Term.t -> r
  val subst : r -> r -> r -> r
  val leaves : r -> r list
  val print : Format.formatter -> r -> unit
  val term_embed : Term.t -> r
end

module type T = sig 
  type r 
  module M : Map.S with type key = r 
  module S : Set.S with type elt = r 
  type t = Rat.t M.t * Rat.t

  val compare : t -> t -> int
  val make : Term.t -> r
  val subst : r -> r -> r -> r
  val leaves : r -> r list
  val term_embed : Term.t -> r
  val print : Format.formatter -> r -> unit
end 

module Type (A:ALIEN) : T with type r = A.r = struct
  type r = A.r
  module M = Map.Make(struct type t = r include A end)
  module S = Set.Make(struct type t = r include A end)
  type t = Rat.t M.t * Rat.t

  let compare (m1,a1) (m2,a2) = 
    let c = Rat.compare a1 a2 in
    if c=0 then M.compare Rat.compare m1 m2 else c

  let make = A.make
  let term_embed = A.term_embed
  let print = A.print
  let subst = A.subst
  let leaves = A.leaves
end

module type TARITH = sig
  include T
  val extract : r -> t option
  val embed : t -> r
end

module Make (X : TARITH) = struct

  module XM = X.M
  module XS = X.S

  let xs_of_list = List.fold_left (fun s x -> XS.add x s) XS.empty

  module P = struct
      
    type t = X.t
	
    let print fmt (m,v) =
      XM.iter 
	(fun t n -> fprintf fmt "%a*%a " Rat.print n X.print t) m;
      fprintf fmt "%a" Rat.print v
	
    let is_num (m,_) = XM.is_empty m
    let is_n v n = Rat.compare n v = 0
      
    let empty_polynome = XM.empty,Rat.zero
      
    let find t m = try XM.find t m with Not_found -> Rat.zero
            
    let mult n (m,a) = 
      if Rat.compare n Rat.zero = 0 then empty_polynome
      else XM.map (Rat.mult n) m , Rat.mult n a
    
    let add (m1,a1) (m2,a2) = 
      let m = 
	XM.fold 
	  (fun x a m -> 
	     let a' = Rat.plus (find x m) a in
	       if Rat.compare a' Rat.zero = 0 then 
		 XM.remove x m else XM.add x a' m)
	  m2 m1
      in m, Rat.plus a1 a2

    let rec mke coef ((m,v) as acc) t =
      let {T.f=sb ; xs=xs} = T.view t in
      match sb , xs with
	| S.Int n , _  -> 
	    m , Rat.plus (Rat.mult coef (Rat.of_int (Hstring.view n))) v
	| S.Rat n , _  -> 
	    m , Rat.plus (Rat.mult coef (Rat.of_rat (Hstring.view n))) v
	| S.Binop S.Mult, [t1;t2] ->
	    let (m1,v1) = mke Rat.one empty_polynome t1 in
	    let (m2,v2) = mke Rat.one empty_polynome t2 in
	    if XM.is_empty m1 then
	      if XM.is_empty m2 then 
		m, Rat.plus v (Rat.mult (Rat.mult coef v1) v2)
	      else 
		add (mult (Rat.mult coef v1) (m2, v2)) acc
	    else 
	      if XM.is_empty m2 then
		add (mult (Rat.mult coef v2) (m1, v1)) acc
	      else 
		let rt = X.term_embed t in
		  XM.add rt (Rat.plus coef (find rt m)) m , v
	| S.Binop S.Div, [t1;t2] -> 
	    let (m1,v1) = mke Rat.one empty_polynome t1 in
	    let (m2,v2) = mke Rat.one empty_polynome t2 in
	    if XM.is_empty m2 then
	      if XM.is_empty m1 then 
		m, Rat.mult coef (Rat.div v1 v2)
	      else 
		add (mult (Rat.div coef v2) (m1, v1)) acc
	    else
	      if XM.is_empty m1 then
		let inv_t2 = T.make (S.Binop S.Div) [T.int "1"; t2] Ty.Tint in
		let rt = X.term_embed inv_t2 in
		XM.add rt (Rat.plus (Rat.mult coef v1) (find rt m))  m , v
	      else
		let rt = X.term_embed t in
		XM.add rt (Rat.plus coef (find rt m)) m , v
	    
	| S.Binop S.Plus , [t1;t2] -> 
	    mke coef (mke coef acc t2) t1
	| S.Binop S.Minus , [t1;t2] -> 
	    mke coef (mke (Rat.minus Rat.zero coef) acc t2) t1
	| S.Binop S.Modulo , [t1;t2] -> 
	    let rt = X.term_embed t in
	    XM.add rt (Rat.plus coef (find rt m)) m , v
	| S.Name _ , _ -> 
	    let rt = X.make t in
	    begin
	      match X.extract rt with
		  Some x -> add (mult coef x) acc
		| None ->
		    let c = Rat.plus (find rt m) coef in
		    if Rat.compare c Rat.zero = 0 then XM.remove rt m , v 
		    else XM.add rt c m , v
	    end
	| _ -> eprintf "%a @." S.print sb; assert false

    let is_mine (m,v as p) = 
      if is_n v Rat.zero then
	let r = ref [] in
	try XM.iter 
	  (fun t v -> 
	     if List.length !r > 1 then raise Exit;
	     if not (is_n v Rat.zero) then
	       if is_n v Rat.one then r:=t::!r else raise Exit) m;
	  (match !r with
	       [t] -> t
	     | _ -> X.embed p)
	with Exit -> X.embed p
      else X.embed p

    let make t = 
      is_mine (mke Rat.one empty_polynome t)

    let embedding r = (XM.add r Rat.one XM.empty), Rat.zero

    let leaves r = 
      match X.extract r with
	  None -> assert false
	| Some (m,v) ->
	    let s = XM.fold (fun t _ -> XS.add t) m XS.empty in
	    let s = 
	      XS.fold 
		(fun a s -> XS.union (xs_of_list (X.leaves a)) s) s XS.empty in
	    XS.elements s
    
    let compare (m1,a1) (m2,a2) = 
      let c = Rat.compare a1 a2 in
      if c=0 then XM.compare Rat.compare m1 m2 else c

    module STR = Set.Make(
      struct
	type t' = T.t * t
	type t = t'
	let compare (t1,r1) (t2,r2) = 
	  let c = T.compare t1 t2 in
	  if c<>0 then compare r1 r2 else c
      end)

    let add_one (m,a) = add (XM.empty,Rat.one) (m,a)

    let choose (m,_) = 
      let tn= ref None in
      (*version I : prend le premier element de la table 
	(try XM.iter (fun k v -> tn:=Some(k,v); raise Exit) m with Exit -> ());
      *)
      
      (*version II : prend le dernier element de la table i.e. le plus grand *)
      (XM.iter (fun k v -> tn:=Some(k,v)) m); 
      match !tn with
	  Some p -> p
	| _ -> raise Not_found



    let subst x t ((m2,v2) as p2) =
      let (m,v) = 
	try
	  let a = XM.find x m2 in
	  let p = match X.extract t with Some p -> p | None -> (embedding t) in
	  add (mult a p) (XM.remove x m2,v2)
	with Not_found -> p2 in
      let p = 
	XM.fold 
	  (fun k a ((mp,vp) as p) -> 
	     let k' = X.subst x t k in
	     match X.extract k'  with 
		 Some p' -> add p (mult a p')
	       | None -> 
		   let a' = Rat.plus a (find k' mp) in
		   if Rat.compare a' Rat.zero = 0 then XM.remove k' mp , vp
		   else XM.add k' a' mp , vp)
	  m (XM.empty,v) in
      is_mine p
	
    let canon (m,v) f = 
      XM.fold 
	(fun x a poly -> 
	   let r = 
	     try f x 
	     with Not_found -> 
	       (XM.add x Rat.one XM.empty), Rat.zero
	   in
	   add (mult a r) poly
	)
	m (XM.empty,v)

    let solve r1 r2 = 
      if debug_fm then eprintf "[fm] we assume %a=%a@." X.print r1 X.print r2;
      let p1,p2 = 
	match (X.extract r1 , r1) ,(X.extract r2,r2) with
	    (Some p1,_) , (Some p2,_) ->  p1 , p2
	  | (Some p1,_) , (None,r) | (None,r) , (Some p1,_) -> p1 , embedding r
	  | (None,_) , (None,_) -> assert false
      in
      let ((m,v) as r) = add p1 (mult (Rat.of_int "-1") p2) in
      try 
	 let x , a = choose r in
	 let p = mult (Rat.opp_inverse a) (XM.remove x m,v) in
	 [x , is_mine p]
      with Not_found -> 
	if Rat.compare v Rat.zero <> 0 then raise Exception.Unsolvable; 
	[]
	
  end

  include P

  type r = X.r

  let is_mine_hs t =  
    match  T.view t with
      | {T.f=Symbols.Int _} 
      | {T.f=Symbols.Rat _} 
      | {T.f=Symbols.Binop 
	    (Symbols.Plus | Symbols.Minus | Symbols.Mult 
	    | Symbols.Div | Symbols.Modulo)} -> true
      | _ -> false

  let is_mine_a a = 
    match Literal.view a with
      | Literal.Builtin (_,p,_) -> is_le p || is_lt p
      | _ -> false

  let is_mine_type r = true

  let normal_form a = 
    match A.view a with
	A.Builtin(false,n,[t1;t2]) when is_le n && T.is_int t1 ->
	  A.make (A.Builtin(true,n,[t2;T.pred t1]))
      | A.Builtin(false,n,[t1;t2]) when is_le n -> 
	  A.make (A.Builtin(true,alt,[t2;t1]))
      | A.Builtin(false,n,[t1;t2]) when is_lt n ->
	  A.make (A.Builtin(true,ale,[t2;t1]))
      | _ -> a
	  
  let name = "arith "

  let type_infos _ = Ty.Trat

  module R = struct
    type elt = t

    module SP = Set.Make (P)

    type ineq = { i: t ; d: SA.t ; le: bool (*true: <=*) }
	
    module SPA ( E : sig type g end) = struct
      include Set.Make
	(struct 
	   type t = A.t * E.g
	   let compare (a1,_) (a2,_) = A.compare a1 a2
	 end)
      let extract s =  fold (fun (_,e) inqs -> e::inqs) s []
    end

    module SPAi = SPA(struct type g=ineq end)
    module SPAii = SPA(struct type g=ineq * ineq end)

    type t = { 
      inqs : SPAi.t;
      monomes : XS.t ; 
      tighten : SPAii.t }
      
    let empty _ = { 
      inqs = SPAi.empty ; 
      monomes = XS.empty ; 
      tighten = SPAii.empty  }

    let add_monomes env (m,_) = 
      {env with monomes = XM.fold (fun t _ -> XS.add t) m env.monomes }
          
    let checking_monomes env (_,(ip1,ip2)) =
      let leaves (m,v) = 
	let s = XM.fold (fun t _ -> XS.add t) m XS.empty in XS.elements s 
      in
      let check_rec = 
	List.iter (fun t -> if XS.mem t env.monomes then raise Exit)
      in
      try
	check_rec (leaves ip1.i);
	check_rec (leaves ip2.i);
	false
      with Exit -> true

    let reconsidering env all_done = 
      SPAii.diff (SPAii.filter (checking_monomes env) env.tighten) all_done

    let remove_sa env sa = 
      let i = { i=Obj.magic 0; d=SA.empty ; le=true} in
      SA.fold 
	(fun a env -> {env with inqs = SPAi.remove (a,i) env.inqs }) sa env

    let is_simple (m,a) k d = 
      XM.is_empty m && ( 
	(k && Rat.compare a Rat.zero <= 0) || 
	  (not k && Rat.compare a Rat.zero <0 ) || raise (NotConsistent d))
      
    let is_eq (m,a) k =  k && XM.is_empty m && Rat.compare a Rat.zero = 0

    let cross x cpos = 
      let cpos = 
	List.map (fun ({i=(m,_)} as e) -> XM.find x m ,e ) cpos in
      let rec cross_rec r = function 
	|	[] -> r
	| {i=(m,_) as i1;d=d1;le=k1} :: l -> 
	    let n1 = XM.find x m in
	    let r = 
	      List.fold_left 
		(fun r (n2,{i=i2;d=d2;le=k2}) ->
		   let ni = 
		     { i=add (mult (Rat.abs n2) i1) 
			 (mult (Rat.abs n1) i2);
		       d=SA.union d1 d2;
		       le=k1&&k2}
		   in ni::r) r cpos
	    in cross_rec r l
      in cross_rec []

    let split x = 
      let rec split_rec ((cp,cn,co) as r) = function
	  [] -> r
	| ({i=(m,_)} as e)::l -> 
	    let r = (
	      try 
		if Rat.compare (XM.find x m) Rat.zero > 0 then e::cp , cn , co 
		else cp , e::cn , co
	      with Not_found -> cp , cn , e::co)
	    in split_rec r l
      in split_rec ([],[],[])
   
    let fm = 
      let rec fourier r l = match l with
	  [] -> r
	| {i=i; d=d; le=k} :: l' when is_simple i k d ->
	    fourier (if is_eq i k then SA.union d r else r) l'
	| {i=i; d=d; le=k} :: _  ->
	    let x,_ = choose i in
	    let cpos , cneg , others = split x l in
	    let ninqs = cross x cpos cneg in
	    fourier r (ninqs@others)
      in fourier SA.empty 
	 
    let assume_le_lt env leqs = 
      let env = 
	List.fold_left
	  (fun env ((a,_) as ai) ->
	     if debug_fm then eprintf "[fm] we assume %a@." A.print a;
	     {env with inqs=SPAi.add ai (SPAi.remove ai env.inqs) }
	  ) env leqs
      in
      env , fm (SPAi.extract env.inqs)
      
    let backtrack_neq env sa a ip1 ip2 =
      let env'  = 
	{ env with tighten=SPAii.remove (a,(ip1,ip2)) env.tighten } in
      let env1 = 
	add_monomes { env' with inqs = SPAi.add (a,ip1) env'.inqs } ip1.i in
      let env2 = 
	add_monomes { env' with inqs = SPAi.add (a,ip2) env'.inqs } ip2.i in
      try 
	let r = fm (SPAi.extract env1.inqs) in
	(try
	   let _ = fm (SPAi.extract env2.inqs) in 
	   if debug_fm then Format.eprintf "[fm] We delay %a@." A.print a;
	   env ,  sa
	 with NotConsistent _ -> env1 , SA.union r sa)
      with NotConsistent _ -> 
	env2 , SA.union sa (fm (SPAi.extract env2.inqs))
      
    let assume_neqs = 
      let rec assume_rec all_done env sa neqs = 
	let todo , delay = SPAii.partition (checking_monomes env) neqs in
	let rc = reconsidering env all_done in
	let todo = SPAii.union rc todo in
	if SPAii.is_empty todo then env , sa    
	else 
	  let env , sa = 
	    SPAii.fold
	      (fun (a,(ip1,ip2)) (env,sa) ->
		 if debug_fm then 
		   Format.eprintf "[fm] We try %a@." A.print a;
		 backtrack_neq env sa a ip1 ip2) todo (env,sa)
	  in
	  assume_rec (SPAii.union rc all_done) env sa delay
      in assume_rec SPAii.empty

    let new_equalities sa = 
      SA.fold (fun a saeq -> match A.view a with
		   A.Builtin(_,n,[t1;t2]) when is_le n -> 
		     SAEq.add (a,t1,t2) saeq
		 | _ -> saeq) sa SAEq.empty

    let is_num t = T.is_int t || T.is_rat t

    let assume env sa repr _ = try
      let env , neqs , ineqs = 
	SA.fold
	  (fun a (env , neqs , ineqs) ->
	     match A.view a with
	       | A.Builtin(_,n,[t1;t2]) when is_le n || is_lt n ->
		   let p = 
		     add (repr t1) (mult Rat.minusone (repr t2)) in
		   let ai = a , {i=p; d=SA.singleton a; le=is_le n} in
		   add_monomes env p , neqs , ai::ineqs

	       | A.Neq(t1,t2) when is_num t1 && is_num t2 -> 
		   let r1 , r2 = repr t1 , repr t2 in
		   let p1 = add r1 (mult Rat.minusone r2) in
		   let p2 = add r2 (mult Rat.minusone r1) in
		   let p1 , p2 = 
		     if not(T.is_int t1) then p1,p2
		     else add_one p1 , add_one p2 in
		   let ip1 = {i=p1; d=SA.singleton a; le=true } in
		   let ip2 = {i=p2; d=SA.singleton a; le=true } in
		   let env = 
		     { env with tighten = SPAii.add (a,(ip1,ip2)) env.tighten }
		   in
		   env , SPAii.add (a,(ip1,ip2)) neqs , ineqs

	       | _ -> (env , neqs , ineqs) ) sa (env,SPAii.empty,[])
      in
      let env , sa = assume_le_lt env ineqs in
      let env , sa = assume_neqs env sa neqs in
      remove_sa env sa , (new_equalities sa)
    with NotConsistent _ ->  raise Exception.Inconsistent

    let query a repr cl env = 
      try 
	let a = normal_form a in
	ignore(assume env (SA.singleton a) repr cl); 
	false 
      with Exception.Inconsistent -> true
	
  end

end
