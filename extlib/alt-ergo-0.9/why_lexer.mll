(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2009                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(* $Id: why_lexer.mll,v 1.9 2009-07-16 13:36:12 conchon Exp $ *)

{
  open Lexing
  open Why_parser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "and", AND;
        "array", ARRAY;
	"as", AS;
	"axiom", AXIOM;
        "bool", BOOL;
        "else", ELSE;
	"exists", EXISTS;
	"external", EXTERNAL;
        "false", FALSE;
	"forall", FORALL;
	"function", FUNCTION;
	"goal", GOAL;
	"if", IF;
	"int", INT;
	"bitv", BITV;
	"logic", LOGIC;
	"logic_ac", LOGIC_AC;
	"not", NOT;
	"or", OR;
	"parameter", PARAMETER;
	"predicate", PREDICATE;
	"prop", PROP;
	"real", REAL;
	"then", THEN;
	"true", TRUE;
	"type", TYPE;
	"unit", UNIT;
	"void", VOID]
	       
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  exception Lexical_error of string

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

  let num0 = Num.Int 0
  let num10 = Num.Int 10
  let num16 = Num.Int 16

  let decnumber s =
    let r = ref num0 in
    for i=0 to String.length s - 1 do
      r := Num.add_num (Num.mult_num num10 !r) 
	(Num.num_of_int (Char.code s.[i] - Char.code '0'))
    done;
    !r

  let hexnumber s =
    let r = ref num0 in
    for i=0 to String.length s - 1 do
      let c = s.[i] in
      let v = 
	match c with
	  | '0'..'9' -> Char.code c - Char.code '0'
	  | 'a'..'f' -> Char.code c - Char.code 'a' + 10
	  | 'A'..'F' -> Char.code c - Char.code 'A' + 10
	  | _ -> assert false
      in
      r := Num.add_num (Num.mult_num num16 !r) (Num.num_of_int v)
    done;
    !r
    
}

let newline = '\n'
let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z']
let letter = alpha | '_'
let digit = ['0'-'9']
let hexdigit = ['0'-'9''a'-'f''A'-'F']
let ident = letter (letter | digit | '\'')*

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | ident as id  
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | digit+ as s
      { INTEGER s }
  | (digit+ as e) '.' (digit* as d)
      { let s = "1"^(String.make (String.length d) '0') in
	FLOAT(e^d^"/"^s) }
  | "0x" (hexdigit+ as e) ('.' (hexdigit* as f))?
      ['p''P'] (['+''-']? as sign) (digit+ as exp) 
      { (* Format.eprintf "hex num found: %s" (lexeme lexbuf); *)
	let f = match f with None -> "" | Some f -> f in
	let v =
	  match sign with
	    | "-" ->
		Num.div_num (hexnumber (e^f)) 
		  (Num.power_num (Num.Int 2) (decnumber exp))
	    | _ -> 
		Num.mult_num (hexnumber (e^f)) 
		  (Num.power_num (Num.Int 2) (decnumber exp))
	in
	let v = 
	  Num.div_num v 
	    (Num.power_num (Num.Int 16) (Num.num_of_int (String.length f))) 
	in
	(* Format.eprintf " -> value = %s@." (Num.string_of_num v); *)
	NUM v
      } 
  | "(*"
      { comment lexbuf; token lexbuf }
  | "'"
      { QUOTE }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | "->"
      { ARROW }
  | "<->"
      { LRARROW }
  | "="
      { EQUAL }
  | "<"
      { LT }
  | "<="
      { LE }
  | ">"
      { GT }
  | ">="
      { GE }
  | "<>"
      { NOTEQ }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { TIMES }
  | "/"
      { SLASH }
  | "%"
      { PERCENT }
  | "@"
      { AT }
  | "."
      { DOT }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "{"
      { LEFTBR }
  | "}"
      { RIGHTBR }
  | "|"
      { BAR }
  | "^"
      { HAT }
  | "\""
      { Buffer.clear string_buf; string lexbuf }
  | eof 
      { EOF }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }

and comment = parse
  | "*)" 
      { () }
  | "(*" 
      { comment lexbuf; comment lexbuf }
  | newline 
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Lexical_error "unterminated comment") }
  | _ 
      { comment lexbuf }

and string = parse
  | "\""
      { STRING (Buffer.contents string_buf) }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline 
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Lexical_error "unterminated string") }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }



