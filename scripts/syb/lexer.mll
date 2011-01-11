{
open Format
open Parser

let hash_of_list lst =
  let r = Hashtbl.create (2 * List.length lst) in
  List.iter (fun (k, v) -> Hashtbl.add r k v) lst; r

let keyword_table = hash_of_list [
  ("and", AND);
  ("of", OF);
  ("type", TYPE);
  ("val", VAL)
]
}

let id_letter = ['a'-'z' 'A'-'Z' '_' '\'']

rule token = parse
    ['a'-'z'] id_letter* as s
      {try Hashtbl.find keyword_table s with Not_found -> LIDENT s}
  | ['A'-'Z'] id_letter* as s
      {try Hashtbl.find keyword_table s with Not_found -> UIDENT s}
  | eof {EOF}
  | "(*" {comment lexbuf; token lexbuf}
  | "|" {BAR}
  | "=" {EQUAL}
  | ":" {COLON}
  | "*" {STAR}
  | "(" {LP}
  | ")" {RP}
  | '.' {DOT}
  | "->" {ARROW}
  | '\n' {Lexing.new_line lexbuf; token lexbuf}
  | _ (*DBG as x *) {
    (*DBG eprintf "ignore `%c' (%d)@." x (Char.code x); *)
    token lexbuf}
and comment = parse
    "*)" {()}
  | "(*" {comment lexbuf; comment lexbuf}
  | '\n' {Lexing.new_line lexbuf; comment lexbuf}
  | _ {comment lexbuf}
