(********************************************************
   This file is part of jStar
        src/utils/persistentarray.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


module type GrowablePersistentArray =
  sig
    type 'a t
    val set : 'a t -> int -> 'a -> 'a t
    val get : 'a t -> int -> 'a
    val create : (int -> 'a) -> 'a t
    val size : 'a t -> int
    val grow : 'a t -> int -> 'a t
    val unsafe_create : 'a array -> (int -> 'a) -> 'a t
  end
module GrowablePersistentImpl : GrowablePersistentArray
