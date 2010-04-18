(********************************************************
   This file is part of jStar 
	src/symbexe/cfg_core.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)


open Pprinter_core
open Methdec_core

let cfg_debug () = false

(** Fills the [succs] and [preds] fields of [stmts] by adding edges
    corresponding to program order and to goto-s. *)
let stmts_to_cfg (stmts : stmt_core list) : unit =
  let l2s = Hashtbl.create 11 in (* maps labels to statements *)
  let al = function
    | {skind = Label_stmt_core l} as s -> Hashtbl.add l2s l s
    | _ -> () in
  let rec process =
    let connect m n = (* adds an edge from [m] to [n] *)
      m.succs <- n :: m.succs; n.preds <- m :: n.preds in
    let find l = (* looks up [l] in [l2s] and reports an error if not found *)
      try Hashtbl.find l2s l
      with Not_found -> Format.eprintf "Undefined label %s.@." l; assert false in
    function
    | {skind = Goto_stmt_core ls} as m :: ss -> 
        List.iter (fun ln -> connect m (find ln)) ls; process ss
    | m :: ((n :: _) as ss)-> connect m n; process ss
    | _ -> () in
  assert (List.for_all (fun s -> s.succs = [] && s.preds = []) stmts);
  List.iter al stmts;
  process stmts

(* ================== BEGIN of Printing dotty files ================== *)

(* stmtsname is a list of programs and names, such that each program's
   cfg is printed in a subgraph with its name.*)
let print_icfg_dotty (stmtsname : (stmt_core list * string) list) (filename : string) : unit =
  (* Print an edge between to stmts *)
  let d_cfgedge chan src dest =
    Printf.fprintf chan "\t\t%i -> %i\n" src.sid dest.sid in
  (* Print a node and edges to its successors *)
  let d_cfgnode chan (s : stmt_core) =
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      s.sid 
      s.sid 
      (Dot.escape_for_label (Debug.toString pp_stmt_core s.skind));
    List.iter (d_cfgedge chan s) s.succs  in

  if cfg_debug () then ignore (Printf.printf "\n\nPrinting iCFG as dot file...");
  let chan = open_out (filename ^ ".icfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  List.iter 
    (fun (stmts,name) -> 
      stmts_to_cfg stmts;
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (Dot.escape_for_label name);
      List.iter (d_cfgnode chan) stmts;
      Printf.fprintf chan  "\t}\n";
    ) 
    stmtsname;
  Printf.fprintf chan  "}\n";
  close_out chan;
  if cfg_debug() then ignore (Printf.printf "\n\n Printing dot file done!")

(* ================== END of Printing dotty files ================== *)




