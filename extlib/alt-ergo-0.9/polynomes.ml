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

module T = Term
module S = Symbols

module type COEF = sig
  type t
  val of_int : string -> t
  val zero : t
  val one : t 
  val minusone : t 
  val plus : t -> t -> t
  val minus : t -> t -> t
  val mult : t -> t -> t
  val inverse : t -> t

  val compare : t -> t -> int

  val print : Format.formatter -> t -> unit
end

module type S = sig

  type coef
  module XM : Map.S
  module X : Sig.COMBINATOR

  type view = coef XM.t * coef
  type t

  val is_num : t -> bool
  
  val make : Term.t -> (t,X.r) Sig.mine
  val embedding : X.r -> t

  val leaves : t -> XM.key list

  val view : t -> view

  val compare : t -> t -> int

  val mult : coef -> t -> t
  val add : t -> t -> t
  val add_one : t -> t

  val choose : t -> X.r * coef
  val subst : X.r -> t -> t -> (t,X.r) Sig.mine
  val canon : t -> (X.r -> t) -> t 
  val solve : t -> t -> (X.r * (t,X.r) Sig.mine) list

  val print : Format.formatter -> t -> unit
end

module Make (C:COEF)(X:Sig.COMBINATOR) = struct

  type coef = C.t

  module X = X
  module XM = Map.Make(struct type t = X.r let compare = X.compare end)
  module XS = Set.Make(struct type t = X.r let compare = X.compare end)

  type view = coef XM.t * coef
  type t = coef XM.t * coef

  let print fmt (m,v) =
    XM.iter 
      (fun t n -> fprintf fmt "%a*%a " C.print n X.print t) m;
    fprintf fmt "%a" C.print v

  let is_num (m,_) = XM.is_empty m
  let is_n v n = C.compare n v = 0

  let empty_polynome = XM.empty,C.zero

  let find t m = try XM.find t m with Not_found -> C.zero

  let mult_map m v k =  XM.map (fun v->C.mult k v) m , C.mult k v

  let merge_map = 
    XM.fold 
      (fun x v m -> 
	 let coef = C.plus (find x m) v in
	 if C.compare coef C.zero = 0 then XM.remove x m
	 else XM.add x (C.plus (find x m) v) m)

  let rec mke coef ((m,v) as acc) t =
    let {Term.f=sb ; xs=xs} = Term.view t in
    match sb , xs with
      | S.Int n , _  -> 
	  m , C.plus (C.mult coef (C.of_int (Hstring.view n))) v
      | S.Binop S.Mult, [t1;t2] ->
	  let (m1,v1) = mke C.one empty_polynome t1 in
	  let (m2,v2) = mke C.one empty_polynome t2 in
	  if XM.is_empty m1 then
	    if XM.is_empty m2 then 
	      m, C.plus v (C.mult (C.mult coef v1) v2)
	    else 
	      if C.compare v1 C.zero = 0 then m,v 
	      else 
		let m2,v2 = mult_map m2 v2 (C.mult coef v1) in
		merge_map m2 m , C.plus v2 v
	  else 
	    if XM.is_empty m2 then
	      if C.compare v2 C.zero = 0 then m,v 
	      else 
		let m1,v1 = mult_map m1 v1 (C.mult coef v2) in
		merge_map m1 m , C.plus v1 v
	    else 
	      let rt = X.empty_embedding t in
	      let c = try XM.find rt m with Not_found -> C.zero in
	      XM.add rt (C.plus coef c) m , v
      | S.Binop S.Div, [t1;t2] -> 
	  let rt = X.empty_embedding t in
	  let c = try XM.find rt m with Not_found -> C.zero in
	  XM.add rt (C.plus coef c) m , v
      | S.Binop S.Plus , [t1;t2] -> 
	  mke coef (mke coef acc t2) t1
      | S.Binop S.Minus , [t1;t2] -> 
	  mke coef (mke (C.minus C.zero coef) acc t2) t1
      | S.Name _ , _ -> 
	  let rt = X.make t in
	  let c = C.plus (find rt m) coef in
	  if C.compare c C.zero = 0 then XM.remove rt m , v 
	  else XM.add rt c m , v
      | _ -> eprintf "%a @." S.print sb; assert false
	  

  let is_mine (m,v as p) = 
    if is_n v C.zero then
      let r = ref [] in
	try XM.iter 
	  (fun t v -> 
	     if List.length !r > 1 then raise Exit;
	   if not (is_n v C.zero) then
	     if is_n v C.one then r:=t::!r else raise Exit) m;
	  (match !r with
	       [t] -> Sig.No t
	     | _ -> Sig.Yes p)
	with Exit -> Sig.Yes p
    else Sig.Yes p


  let make t =  is_mine (mke C.one empty_polynome t)

  let embedding r = (XM.add r C.one XM.empty), C.zero

  let view x = x

  let leaves (m,v) = 
    let s = XM.fold (fun t _ -> XS.add t) m XS.empty in
    XS.elements s
    
  let compare (m1,a1) (m2,a2) = 
    let c = C.compare a1 a2 in
    if c=0 then XM.compare C.compare m1 m2 else c

  module STR = Set.Make(
    struct
      type t' = Term.t * t
      type t = t'
      let compare (t1,r1) (t2,r2) = 
	let c = Term.compare t1 t2 in
	if c<>0 then compare r1 r2 else c
    end)

  module Set = 
    Set.Make(struct type t'=t type t=t' let compare=compare end)

  module Map = 
    Map.Make(struct type t'=t type t=t' let compare=compare end)

  let mult n (m,a) = XM.map (C.mult n) m , C.mult n a
      
  let add (m1,a1) (m2,a2) = 
    let m = 
      XM.fold 
	(fun x a m -> 
	   let v = try XM.find x m with Not_found -> C.zero in
	   let a' = C.plus v a in
	   if C.compare a' C.zero = 0 then 
	     XM.remove x m else XM.add x a' m)
	m2 m1 
    in m , C.plus a1 a2

  let add_one (m,a) = add (XM.empty,C.one) (m,a)

  let choose (m,_) = 
    let tn= ref None in
    (try XM.iter (fun k v -> tn:=Some(k,v); raise Exit) m
     with Exit -> ());
    match !tn with
	Some p -> p
      | _ -> raise Not_found

  let subst x p1 ( (m2,v2) as p2) =
    let p = 
      try
	let a = XM.find x m2 in
	  add (mult a p1) (XM.remove x m2,v2)
      with Not_found -> p2 in
      is_mine p
	
  let canon (m,v) f = 
    XM.fold 
      (fun x a poly -> 
	 let r = 
	   try f x 
	   with Not_found -> 
	     (XM.add x C.one XM.empty), C.zero
	 in
	 add (mult a r) poly
      )
      m (XM.empty,v)

  let solve r1 r2 = 
    if debug_fm then eprintf "[fm] we assume %a=%a@." print r1 print r2;
    let ((m,v) as r) = add r1 (mult (C.of_int "-1") r2) in
    try 
      let x , a = choose r in
      [x , is_mine (mult (C.inverse a) (XM.remove x m,v))]
    with Not_found -> 
      if C.compare v C.zero <> 0 then raise Exception.Unsolvable; []
	
end

