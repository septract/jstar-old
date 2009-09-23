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

module rec CX : sig
  include Sig.X

  val extract1 : r -> X1.t option
  val embed1 : X1.t -> r

  val extract2 : r -> (r Pairs.abstract) option
  val embed2 : r Pairs.abstract -> r

  val extract3 : r -> (r Bitv.abstract) option
  val embed3 : r Bitv.abstract -> r

end =
struct

  (* Xi < Term < Exist < Ac *)
  type r =
    | X1    of X1.t 
    | X2    of X2.t 
    | X3    of X3.t 
    | Term  of Term.t
    | Exist of r
    | Ac    of AC.t
    
  let extract1 = function X1 r   -> Some r | _ -> None
  let extract2 = function X2 r   -> Some r | _ -> None
  let extract3 = function X3 r   -> Some r | _ -> None
  
  let embed1 x = X1 x
  let embed2 x = X2 x
  let embed3 x = X3 x
	
  let is_an_eq a = 
    match Literal.view a with Literal.Builtin _ -> false | _ -> true

  let normal_form a =
    if X1.is_mine_a a then X1.normal_form a 
    else if X2.is_mine_a a then X2.normal_form a 
    else if X3.is_mine_a a then X3.normal_form a 
    else  a
      
      
  let rec compare a b = 
    let c = compare_tag a b in 
    if c = 0 then comparei a b else c

  and compare_tag a b = 
    Pervasives.compare (theory_num a) (theory_num b)
      
  and comparei a b = 
    match a, b with
      | X1 x, X1 y -> X1.compare x y
      | X2 x, X2 y -> X2.compare x y
      | X3 x, X3 y -> X3.compare x y
      | Term x  , Term y  -> Term.compare x y
      | Ac x    , Ac    y -> AC.compare x y
      | Exist x , Exist y -> compare a b
      | _                 -> assert false

  and theory_num x = Obj.tag (Obj.repr x)

  module MR = Map.Make(struct type t = r let compare = compare end)
    
  let rec print fmt = function
    | X1 t    -> fprintf fmt "X1(%s):%a" X1.name X1.print t
    | X2 t    -> fprintf fmt "X2(%s):%a" X2.name X2.print t
    | X3 t    -> fprintf fmt "X3(%s):%a" X3.name X3.print t
    | Term t  -> fprintf fmt "Empty:%a" Term.print t
    | Ac t    -> fprintf fmt "%a" AC.print t
    | Exist v -> fprintf fmt "%a" print v


  let leaves r = match r with 
    | X1 _ -> X1.leaves r 
    | X2 _ -> X2.leaves r 
    | X3 _ -> X3.leaves r 
    | Ac t -> r :: (AC.leaves t)
    | Term _  | Exist _ -> [r]

  let exist_embed r = 
    match r , leaves r with
      | (Exist _ | Term _ | Ac _) , _ -> assert false
      | _ , [r'] when compare r r' = 0 -> Exist r
      | _ -> assert false

  let ac_extract = function Ac r   -> Some r | _ -> None
  let ac_embed x = Ac x
  let term_embed t = Term t

  let subst p v r = 
    if compare p v = 0 then r 
    else match r with
      | X1 t1   -> X1.subst p v t1
      | X2 t2   -> X2.subst p v t2
      | X3 t3   -> X3.subst p v t3
      | Ac t    -> if compare p r = 0 then v else AC.subst p v t
      | Term  _ -> if compare p r = 0 then v else r
      | Exist _ -> if compare p r = 0 then v else r
	  
	
  let make t = 
    match X1.is_mine_hs t,X2.is_mine_hs t,X3.is_mine_hs t,AC.is_mine_hs t with
      true  , false , false, false  -> X1.make t
    | false , true  , false, false  -> X2.make t
    | false , false , true , false  -> X3.make t
    | false , false , false, true   -> AC.make t
    | false , false , false, false  -> Term t
    | _ -> assert false

  let add_mr =
    List.fold_left 
      (fun solved (p,v) -> 
	 MR.add p (v::(try MR.find p solved with Not_found -> [])) solved)

  let is_empty = function 
      Term _ | Exist _ | Ac _ -> true | _ -> false

  let partition tag = 
    List.partition 
      (fun (u,t) -> 
	 (theory_num u = tag || is_empty u) && 
	   (theory_num t = tag || is_empty t))

  let rec solve_list solved l =
    List.fold_left
      (fun solved (a,b) -> 
	 if compare a b = 0 then solved else
	   match a , b with
	       (* both sides are empty *)
	     | (Term _ | Exist _ | Ac _) , (Term _ | Exist _ | Ac _) -> 
		 add_mr solved [a,b]

	     (* only one side is empty *)
	     | (a, b) when is_empty a || is_empty b ||  compare_tag a b = 0 ->
		 let a,b = if is_empty a then b,a else a,b in
		 let cp , sol = partition (theory_num a) (solvei b a) in
		 solve_list (add_mr solved cp) sol
		   
	     (* both sides are not empty *)
	     | a , b -> solve_theoryj solved a b
      ) solved l

  and solve_theoryj solved xi xj =
    let cp , sol = partition (theory_num xj) (solvei xi xj) in
    solve_list (add_mr solved cp) (List.rev_map (fun (x,y) -> y,x) sol)

  and solvei a b =
    match b with
      | X1 _ -> X1.solve a b
      | X2 _ -> X2.solve a b
      | X3 _ -> X3.solve a b
      | Term _ | Exist _ | Ac _ -> 
	  fprintf fmt "solvei %a = %a @." print a print b;
	  assert false

  let rec solve_rec mt ab = 
    let mr = solve_list mt ab in
    let mr , ab = 
      MR.fold 
	(fun p lr ((mt,ab) as acc) -> match lr with
	     [] -> assert false
	   | [_] -> acc
	   | x::lx -> 
	       MR.add p [x] mr , List.rev_map (fun y-> (x,y)) lx)	 
	mr (mr,[])
    in 
    if ab=[] then mr else solve_rec mr ab
      
  let solve a b =
    MR.fold 
      (fun p lr ret -> 
	 match lr with [r] -> (p ,r)::ret | _ -> assert false) 
      (solve_rec MR.empty [a,b]) []

  let rec type_infos = function
      X1 t1   -> X1.type_infos t1
    | X2 t2   -> X2.type_infos t2
    | X3 t3   -> X3.type_infos t3
    | Ac x    -> AC.type_infos x
    | Term t -> let {Term.ty = ty} = Term.view t in ty
    | Exist x -> type_infos x
	
  module R =
  struct
    type elt = r
    type t = { r1: X1.R.t ; r2: X2.R.t ; r3: X3.R.t}
    let empty _ = {
      r1=X1.R.empty (); 
      r2=X2.R.empty (); 
      r3=X3.R.empty ()
    }

    let make_repr repr = 
      let repr1 x = 
	match repr x with 
	    X1 v -> v 
	  | t -> X1.embedding t in
      let repr2 x = 
	match repr x with 
	    X2 v -> v 
	  | Term _ as t -> X2.embedding t
	  | _ -> raise Not_found in
      let repr3 x = 
	match repr x with 
	    X3 v -> v 
	  | Term _ as t -> X3.embedding t
	  | _ -> raise Not_found in
      repr1, repr2, repr3
	
    let assume env sa repr cl = 
      let repr1,repr2,repr3 = make_repr repr in
      let env1, seq1 = X1.R.assume env.r1 sa repr1 cl in
      let env2, seq2 = X2.R.assume env.r2 sa repr2 cl in
      let env3, seq3 = X3.R.assume env.r3 sa repr3 cl in
      {r1 = env1; r2 = env2; r3 = env3}, 
      Literal.SetEq.union seq1 (Literal.SetEq.union seq2 seq3)
	
    let query a repr cl env = 
      let repr1,repr2,repr3 = make_repr repr in
      if X1.is_mine_a a
      then X1.R.query a repr1 cl env.r1 
      else if X2.is_mine_a a
      then X2.R.query a repr2 cl env.r2
      else if X3.is_mine_a a then X3.R.query a repr3 cl env.r3
      else assert false
  end

end

and TX1 : Arith.T with type r = CX.r = Arith.Type(CX)

and X1 : Sig.THEORY  with type t = TX1.t and type r = CX.r =
  Arith.Make
    (struct
       include TX1
       let extract = CX.extract1
       let embed =  CX.embed1
       let make = CX.make
     end)

and X2 : Sig.THEORY with type r = CX.r and type t = CX.r Pairs.abstract =
  Pairs.Make
    (struct
       include CX
       let extract = extract2
       let embed = embed2
     end)

and X3 : Sig.THEORY with type r = CX.r and type t = CX.r Bitv.abstract =
  Bitv.Make
    (struct
       include CX
       let extract = extract3
       let embed = embed3
     end)

and AC : Ac.SMake with type r = CX.r = Ac.Make(CX)
