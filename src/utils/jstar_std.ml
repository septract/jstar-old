module Int = struct type t = int let compare = compare end
module StringSet = Set.Make (String)
module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)
module IntMap = Set.Make (Int)

let ( @@ ) f g x = f (g x)
let ( & ) f x = f x
let ( |> ) x f = f x
let ( =:: ) xs x = xs := x :: !xs
let ( !* ) = Lazy.force

module CharH = struct
  let is_space =
    let spaces = " \t\n\r\x0b\x0c" in
    fun c -> String.contains spaces c
end

module StringH = struct
  let trim s =
    let n = String.length s in
    let i, j = ref 0, ref (n - 1) in
    while !i < n && CharH.is_space s.[!i] do incr i done;
    if !i = n then ""
    else begin
      while CharH.is_space s.[!j] do decr j done;
      String.sub s !i (!j - !i + 1)
    end

  let starts_with s t =
    let n = String.length t in
    if n > String.length s 
    then false
    else String.sub s 0 n = t

  let ends_with s t =
    let m = String.length s in
    let n = String.length t in
    if n > m
    then false
    else String.sub s (m - n) n = t
end

module MapHelper = functor (M : Map.S) -> struct
  let filter (p : M.key -> 'a -> bool) (map : 'a M.t) : 'a M.t =
    M.fold (fun k v a -> if p k v then M.add k v a else a) map M.empty
end

module ListH = struct
  let init n f =
    let rec loop acc = function
      | 0 -> acc
      | n -> loop (f (n - 1) :: acc) (n - 1) in
    loop [] n
end
