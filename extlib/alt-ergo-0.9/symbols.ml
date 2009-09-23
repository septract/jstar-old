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

open Hashcons

type binop = Plus | Minus | Mult | Div | Modulo | At
type is_ac = bool
type t = 
    Name of Hstring.t * is_ac
  | Int of Hstring.t
  | Rat of Hstring.t
  | Bitv of string
  | Binop of binop 
  | Var of Hstring.t

let unit = Name (Hstring.make "()", false)

let name ?(ac=false) s = Name (Hstring.make s, ac)

let var s = Var (Hstring.make s)
let int i = Int (Hstring.make i)
let rat r = Rat (Hstring.make r)

let is_ac = function
    Name(_,b) -> b
  | _ -> false

let underscoring = function
    Var s -> Var (Hstring.make ("$"^Hstring.view s))
  | _ -> assert false

let shat = name "^"

let plus = Binop Plus
let minus = Binop Minus
let mult = Binop Mult
let div = Binop Div
let modulo = Binop Modulo
let at = Binop At

let compare s1 s2 =  match s1,s2 with
    Name (n1,ac1) , Name (n2,ac2) -> 
      let c = Pervasives.compare ac1 ac2 in
      if c = 0 then Hstring.compare n1 n2 else c
  | Name _ , _ ->  -1
  | _ , Name _ -> 1
  | Var n1 , Var n2 -> Hstring.compare n1 n2
  | Var _ , _ -> -1
  | _ , Var _ -> 1
  | Int i1 , Int i2 -> Hstring.compare i1 i2
  | Int _ , _ -> -1
  | _ , Int _ -> 1
  | _  -> Pervasives.compare s1 s2
  
let equal s1 s2 = compare s1 s2 = 0

let hash = function
    Name (n,ac) -> Hstring.hash n * 19 + (if ac then 1 else 0)
  | Var n (*| Int n*) -> Hstring.hash n * 19 + 1
  | s -> Hashtbl.hash s
	
let to_string =  function
    Name (n,_) -> Hstring.view n
  | Var x -> "'"^(Hstring.view x)^"'"
  | Int n -> Hstring.view n
  | Rat n -> Hstring.view n
  | Bitv s -> "["^s^"]"
  | Binop Plus -> "+" 
  | Binop Minus -> "-" 
  | Binop Mult -> "*"
  | Binop Div -> "/"
  | Binop Modulo -> "%"
  | Binop At -> "@"

let print fmt s = Format.fprintf fmt "%s" (to_string s)

let dummy = Name (Hstring.make "_one", false)

let fresh = 
  let cpt = ref 0 in
  fun s -> incr cpt; name (Format.sprintf "__%s%i" s (!cpt))

module Map =
  Map.Make(struct type t' = t type t=t' let compare=compare end)

module Set = 
  Set.Make(struct type t' = t type t=t' let compare=compare end)

