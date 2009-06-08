{ (******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************)

(* header *)

open Logic_parser 

type error =
  | Illegal_character of char
  | Unterminated_comment

exception Error of error * int * int

(* error reporting *)
open Format

let report_error ppf = function
  | Illegal_character c ->
      fprintf ppf "Illegal character (%s)" (Char.escaped c)
  | Unterminated_comment ->
      fprintf ppf "Comment not terminated"

let incr_linenum lexbuf = 
  let pos = lexbuf.Lexing.lex_curr_p in 
  lexbuf.Lexing.lex_curr_p <- { pos with 
				Lexing.pos_lnum = pos.Lexing.pos_lnum + 1; 
				Lexing.pos_bol = pos.Lexing.pos_cnum; 
			      } 


let keyword_al = [
  ("_",UNDERSCORE);
  ("(",LEFTPAREN);
  (")",RIGHTPAREN);
  ("{",L_BRACE);
  ("}",R_BRACE);
  (",",COMMA);
  (":",COLON);
  (";",SEMICOLON);
  ("*",STAR);
  ("|",BAR);
  ("?",QUESTIONMARK);
  ("=",EQUAL);
  ("!=",NOTEQUAL);
  ("|-",VDASH);
  ("False",FALSE);
  ("True",TRUE);
  ("Implication",IMPLICATION);
  ("Frame",FRAME);
  ("Garbage",GARBAGE);
  ("Inconsistency",INCONSISTENCY);
  ("rule",RULE);
  ("emprule",EMPRULE);
  ("purerule",PURERULE);
  ("if",IF);
  ("without",WITHOUT);  
  ("notin",NOTIN);  
  ("notincontext",NOTINCONTEXT);  
  ("EV",EV);  
  ("where",WHERE);
  ("or",OR);
] 
} 

let  blank = (' ' | '\009' | '\013' | '\010')+  

let  not_cr_lf = [ ^ '\010' '\013']
let  not_star = [ ^ '*']
let  not_star_slash = [^ '*' '/']

let  line_comment = "//" not_cr_lf*

let  newline = ('\013' | '\010' | "\010\013")
let  blank = (' ' | '\009')+  
let  ignored_helper = (blank | line_comment)+


let  dec_digit = ['0' - '9']

let  alpha_char = ['a' - 'z'] | ['A' - 'Z']
  
let  simple_id_char = alpha_char | dec_digit | '_' | '$'

let  first_id_char = alpha_char | '$'

let  identifier = 
      first_id_char (simple_id_char)* 


let  hex_digit = dec_digit | ['a' - 'f'] | ['A' - 'F']
let  hex_constant = '0' ('x' | 'X') hex_digit+

let  quote = '\''

let  escapable_char = '\\' | ' ' | quote | '.' | '#' | '"' | 'n' | 't' | 'r' | 'b' | 'f'
let  escape_code = 'u' hex_digit hex_digit hex_digit hex_digit
let  escape_char = '\\' (escapable_char | escape_code)  

let  string_char = escape_char | ['\000' - '\033'] | ['\035' - '\091'] | ['\093' - '\127']   

let  string = '"' string_char* '"'

rule token = parse
   | newline { incr_linenum lexbuf; token lexbuf } 
   | ignored_helper { token lexbuf } 
   | "/*" { comment lexbuf; token lexbuf }
   | eof { EOF }
   | "_" { UNDERSCORE }
   | "(" { LEFTPAREN }
   | ")" { RIGHTPAREN }
   | "{" { L_BRACE }
   | "}" { R_BRACE }
   | "," { COMMA }   
   | "?" { QUESTIONMARK }   
   | ":" { COLON }   
   | ";" { SEMICOLON }   
   | "*" { STAR }   
   | "|" { BAR }
   | "=" { EQUAL }
   | "!=" { NOTEQUAL }
   | "False" { FALSE }
   | "True" { TRUE }
   | "Implication" {IMPLICATION}
   | "import" {IMPORT}
   | "Import" {IMPORT}
   | "Frame" {FRAME}
   | "rule" {RULE}
   | "emprule" {EMPRULE}
   | "rewrite" {REWRITERULE}
   | "purerule" {PURERULE}
   | "pred" {PRED}
   | "Inconsistency" {INCONSISTENCY}
   | "Abstract" {ABS}
   | "|-" { VDASH }
   | identifier  { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> IDENTIFIER s}
   | string  { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> STRING (String.sub s 1 (String.length s - 2))}
   | _ { raise (Error(Illegal_character ((Lexing.lexeme lexbuf).[0]),
                     Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf)) }
and comment = parse
   | "/*"  { comment lexbuf }
   | "*/"  { }
   | newline  { incr_linenum lexbuf; comment lexbuf }
   | _     { comment lexbuf }  

(* ====================================================================== *)




{ (* trailer *)
}
