module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

let ( |> ) x f = f x
let ( & ) f x = f x
