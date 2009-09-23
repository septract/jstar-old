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

open Options
module L = List
module HS = Hstring

module type SMake = sig 
  type r
  type t = r Sig.ac
  val print : Format.formatter -> t -> unit
  val subst : r -> r -> t -> r 
  val compare : t -> t -> int
  val is_mine_hs :Term.t -> bool
  val make : Term.t -> r
  val type_infos : t -> Ty.t
  val leaves : t -> r list
end

module Make (X : Sig.X) = struct

  type r = X.r
  type t = r Sig.ac
  
  let type_infos t = 
    match snd t with
      | []   -> assert false
      | a::_ -> X.type_infos a

  let is_mine_hs t = 
    match Term.view t with
      |{Term.f=Symbols.Name(_,b)} -> b
      | _ -> false

  let make t = match Term.view t with
    | {Term.f=Symbols.Name(hs,true) ; xs=xs} -> 
	X.ac_embed (hs,L.map X.make xs)
    | _ -> assert false

  let pr_xs fmt = function
      [] -> assert false
    | p::l  -> 
	Format.fprintf fmt "%a" X.print p; 
	L.iter (Format.fprintf fmt ",%a" X.print) l

  let print fmt (hs,xs) = 
    Format.fprintf fmt "Ac:%s(%a)" (HS.view hs) pr_xs xs

  let rev_sort l = L.rev (L.fast_sort X.compare l)

  let rec mset_cmp = function
    | []  ,  [] ->  0
    | a::r,b::s -> let c = X.compare a b in if c<>0 then c else mset_cmp(r,s)
    | _ -> assert false

  let compare (hs1,xs1) (hs2,xs2) = 
    let c = HS.compare hs1 hs2 in
    if c <> 0 then c 
    else let c = L.length xs1 - List.length xs2 in
    if c<> 0 then c else mset_cmp (rev_sort xs1,rev_sort xs2)

  let subst p v (hs,xs) =
    if debug_ac then
      Format.fprintf fmt "[ac] subst %a |-> %a in %a@."
	X.print p X.print v X.print (X.ac_embed (hs,xs));

    let xs = 
      L.fold_left
	(fun acc r ->
	   let rr = X.subst p v r in
	   match X.ac_extract rr with
	     | Some(hs',xs') when HS.equal hs hs' -> xs' @ acc
	     | _ -> rr :: acc
	)[] xs 
    in
    X.ac_embed (hs,xs)

  let leaves (_,xs) = 
    L.fold_left (fun acc x -> (X.leaves x)@acc) [] xs

end

