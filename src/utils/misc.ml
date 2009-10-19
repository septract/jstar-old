let map_option f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el  with
	None -> rest
   |	Some el -> el::rest) l []

let map_lift_exists f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el, rest  with
	None,_ -> rest
   |	Some el,Some rest -> Some (el::rest)
   |  Some el, None -> Some [el]) l None

let map_lift_forall f l
    =
  List.fold_right 
    (fun el rest-> 
      match f el, rest  with
     	  None,_ -> None
	    | _, None -> None
      |	Some el,Some rest -> Some (el::rest)) l (Some [])


type ('a,'b) sum = 
    Inr of 'a
  | Inl of 'b

let map_sum f l
    =
  List.fold_right
    (fun el (restl,restr) -> 
      match f el with
      | Inl l -> (l::restl,restr)
      | Inr r -> (restl,r::restr)) l ([],[])
