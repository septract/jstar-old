(*
module type AcS_sig = sig
  
  type t 
  type elt = Term.t 
      
  module SetT : Set.S

  val empty : unit -> t
  val add : t -> elt -> t
  val sleaves : t -> Symbols.t -> elt -> SetT.t
  val print : Format.formatter -> t -> unit
end

  
module AcS : AcS_sig = struct
  
  type elt = Term.t  
      
  (** given [p|-> P], this set contains leaves of P **)
  module SetT = Set.Make
    (struct type t = elt let compare = Term.compare end)
    
  (** This map associates each p to leaves(P) **)
  module MT = Map.Make
    (struct type t = Term.t let compare = Term.compare end)
    
  (** This map associates each p to leaves(P) according to an AC symbol **)
  module MS = Map.Make
    (struct type t = Hstring.t let compare = Hstring.compare end)
    
  type t = (SetT.t MT.t) MS.t
      
  let empty _ = assert false
    
  let add  t elt = assert false
    
  let sleaves t s e = assert false
    
  let print fmt t = assert false

end
*)

