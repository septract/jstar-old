(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2009,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


(* Manage methdec infos for a file *) 

open Jparsetree
open Global_types 
open Jimple_global_types



let make_methdec mos cname ty n pars tc locs b  =
{
  modifiers= mos;
  class_name = cname;
  ret_type=ty;
  name_m= n; 
  params= pars;
  locals = locs;
  th_clause=tc;
  bstmts=b 
}

let get_list_methods f = 
  match f with
  | JFile (_,_,_,_,_, meml) -> List.filter (fun a -> match a with 
					    |Field _ -> false
					    |Method _ -> true) meml 

let get_list_member f = 
  match f with
  | JFile (_,_,_,_,_, meml) -> meml

let get_list_fields f = 
  match f with
  | JFile (_,_,_,_,_, meml) -> List.filter (fun a -> match a with 
					    |Field _ -> true
					    |Method _ -> false) meml 

let get_class_name f =
  match f with 
  | JFile(_,_,cn,_,_,_) ->cn


let get_locals b = 
  match b with 
  | None -> []
  | Some body ->
      let dec_or_stmt_list = fst body in
      let dos=List.map (fun a -> match a with 
		   |DOS_dec (Declaration (t,nl)) -> List.map (fun n -> (t,n)) nl
		   | _ -> [] ) dec_or_stmt_list 
      in List.flatten dos



let make_stmts_list b = 
  match b with
  | None -> [] 
  | Some body ->
      let dec_or_stmt_list = fst body in
      let dos=List.map (fun a -> match a with 
		   |DOS_stm s -> [s]
		   | _ -> [] ) dec_or_stmt_list 
      in  List.flatten dos




let member2methdec cname m =
  match m with 
  | Method(mo,t,n,p,thc,mb) -> 
      let locs=get_locals mb in
      let bstmts= make_stmts_list mb in
      Some(make_methdec mo cname t n p thc locs bstmts) 
  | _ -> None



let make_methdecs_of_list cname meml =
  Misc.map_option (member2methdec cname) meml
  

let get_msig m cname =
  (cname,m.ret_type,m.name_m,m.params)




(* ========================  ======================== *) 
