(********************************************************
   This file is part of jStar
        src/utils/persistentarray.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(*   This file contains an implementation of Persistent Array following:
     A Persistent Union-Find Data Structure
     Sylvain Conchon	Jean-Christophe Filliatre
     Workshop on ML'07   

   However, we have extended it to enable the array to be grown dynamically.

*)

(* grow makes all arrays grow, not just current one*)
module type GrowablePersistentArray = sig
  type 'a t
  val set : 'a t -> int -> 'a -> 'a t 
  val get : 'a t -> int -> 'a
  val create :  (int -> 'a) -> 'a t
  val size : 'a t -> int
  val grow : 'a t -> int -> 'a t
  (* Do not use the array you pass in. *)
  val unsafe_create : 'a array -> (int -> 'a) -> 'a t
end

module GrowablePersistentImpl : GrowablePersistentArray =
  struct 
    type 'a t = 'a data ref * int 
    and 'a data = 
	RealArray of 'a array * (int -> 'a)
      |	Diff of int * 'a * 'a t

    (* Make array currently being accessed top *)
    let rec reroot (a,ir') =
      match !a with 
	RealArray(_,_) -> ()
      | Diff(i,x,(b,ir)) -> 
	  reroot (b,ir);
	  match !b with 
	    Diff(_,_,_) -> 
            (* reroot will make top thing the RealArray so not
	       possible for it to be a Diff. *) 
	      assert false
	  | RealArray(c,f) -> 
	      let oldi = Array.get c i in 
	      Array.set c i x;
	      a := RealArray(c,f);
	      b := Diff(i, oldi, (a,ir'))



    let create f = (ref (RealArray (Array.init 2 f, f)), 
		      0)

    let unsafe_create a f = (ref (RealArray (a, f)), 
		      Array.length a) 

    let rec get (a,ir) i = 
      reroot (a,ir);
      match !a with 
	RealArray (a,f) -> Array.get a i 
      |	Diff (j, x, a) -> if i=j then x else get a i  

    let rec set (a,ir) i x = 
      reroot (a,ir);
      match !a with 
	RealArray (a',f) as n -> 
	  let old = Array.get a' i in 
	  if old <> x then  
	    begin
	      Array.set a' i x;
	      let na = ref n,ir in
	      a := Diff(i,old,na);
	      na
	    end
	  else 
	    (a,ir)
      |	_ -> ref (Diff (i,x,(a,ir))), ir



    (* Helper functions for accessing the underlying array to allow it
    to be resized. *)
    let rec real_array ((a,ir) : 'a t) = 
      match !a with 
	RealArray(_,_) -> a
      | Diff(i,x,a) -> real_array a

    let real_size (a,ir) = 
      let ra = real_array (a,ir) in
      match !ra with 
	RealArray (a,f) -> Array.length a 
      |	Diff(_,_,_) -> assert false

    let size (a,ir) = ir

    (* Make underlying array twice as large *)
    let double (a,ir) = 
      let ra = real_array (a,ir) in 
      match !ra with 
	RealArray (a,f) -> 
	  let n = Array.length a in 
	  ra := RealArray(Array.init (n*2) (fun i -> if i < n then a.(i) else f(i)),f)
      | Diff(_,_,_) -> assert false 
 
    (* Extend array, possibly growing underlying array if necessary. *)
    let grow t n =
      if size t + n >= real_size t then 
	double t;
      let (a,ir) = t in 
      let size = ir in 
      (a,size+n)

  end

