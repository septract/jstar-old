(********************************************************
   This file is part of jStar
        src/jimplefront/translatejimple.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


exception Contained
val conjoin_with_res_true : Psyntax.pform -> Psyntax.pform
module LocalMap :
  sig
    type key = string
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end
type local_map = Psyntax.args list Javaspecs.AxiomMap.t
val verify_jimple_file :
  Jimple_global_types.jimple_file ->
  Psyntax.logic ->
  Psyntax.logic -> Javaspecs.methodSpecs -> Javaspecs.methodSpecs -> unit
