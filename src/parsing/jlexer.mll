(********************************************************
   This file is part of jStar 
	src/parsing/jlexer.mll
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)


{ (* ddino implementation of a lexer for jimple *)
(* header *)
open Lexing  
open Jparser 

type error =
  | Illegal_character of char
  | Unterminated_comment

exception Error of error * Lexing.lexbuf

let new_line lexbuf =
  let pos =  lexbuf.Lexing.lex_curr_p in 
  lexbuf.Lexing.lex_curr_p <- { pos with 
				Lexing.pos_lnum = pos.Lexing.pos_lnum + 1; 
				Lexing.pos_bol = pos.Lexing.pos_cnum; 
			      } 


let nest_depth = ref 0
let nest_start_pos = ref dummy_pos
let nest x =
  nest_depth := !nest_depth + 1; nest_start_pos := (x.lex_curr_p)
let unnest x = 
  nest_depth := !nest_depth - 1; (!nest_depth)!=0 


let error_message e lb = 
  match e with 
    Illegal_character c -> 
      Printf.sprintf "Illegal character %c found at line %d character %d.\n" 
	c 
	lb.lex_curr_p.pos_lnum 
	(lb.lex_curr_p.pos_cnum - lb.lex_curr_p.pos_bol)
  | Unterminated_comment -> Printf.sprintf "Unterminated comment started at line %d character %d in %s.\n"
	!nest_start_pos.pos_lnum 
	(!nest_start_pos.pos_cnum  - !nest_start_pos.pos_bol)
	lb.lex_curr_p.pos_fname

(* [kwd_or_else d s] is the token corresponding to [s] if there is one,
  or the default [d] otherwise. *)
let kwd_or_else = 
  let keyword_table = Hashtbl.create 53 in
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok) [
    "abstract", ABSTRACT;
    "abstraction", ABSRULE;
    "andalso", ANDALSO;
    "annotation", ANNOTATION;
    "as", AS;
    "axioms", AXIOMS;
    "boolean", BOOLEAN;
    "breakpoint", BREAKPOINT; 
    "byte", BYTE;
    "case", CASE;
    "catch", CATCH;
    "char", CHAR;
    "class", CLASS;
    "cls", CLS;
    "define", DEFINE;
    "double", DOUBLE;
    "emprule", EMPRULE;
    "ensures", ENSURES;
    "enum", ENUM;
    "equiv", EQUIV;
    "export", EXPORT;
    "exports", EXPORTS;
    "extends", EXTENDS;
    "False", FALSE;
    "final", FINAL;
    "float", FLOAT;
    "Frame", FRAME;
    "from", FROM;
    "Garbage", GARBAGE;
    "goto", GOTO;
    "if", IF;
    "implements", IMPLEMENTS;
    "Implication", IMPLICATION;
    "import", IMPORT;
    "invariant", INVARIANT;
    "Inconsistency", INCONSISTENCY;
    "inductive", INDUCTIVE;
    "instanceof", INSTANCEOF ;
    "int", INT;
    "interface", INTERFACE;
    "interfaceinvoke", INTERFACEINVOKE;
    "lengthof", LENGTHOF;
    "long", LONG;
    "lookupswitch", LOOKUPSWITCH;
    "native", NATIVE;
    "new", NEW;
    "newarray", NEWARRAY;
    "newmultiarray", NEWMULTIARRAY;
    "notin", NOTIN;  
    "notincontext", NOTINCONTEXT;  
    "null", NULL;
    "null_type", NULL_TYPE;
    "old", OLD;
    "or", ORTEXT;
    "private", PRIVATE;
    "protected", PROTECTED;
    "public", PUBLIC;
    "purerule", PURERULE;
    "requires", REQUIRES;
    "return", RETURN;
    "rewrite", REWRITERULE;
    "rule", RULE;
    "short", SHORT;
    "specialinvoke", SPECIALINVOKE;
    "static", STATIC;
    "staticinvoke", STATICINVOKE;
    "strictfp", STRICTFP;
    "synchronized", SYNCHRONIZED;
    "tableswitch", TABLESWITCH;  
    "throw", THROW ;
    "throws", THROWS;
    "to", TO;
    "transient", TRANSIENT;
    "True", TRUE;
    "unknown", UNKNOWN;
    "virtualinvoke", VIRTUALINVOKE;
    "void", VOID;
    "volatile", VOLATILE;
    "where", WHERE;
    "with", WITH;
    "without", WITHOUT;
  ];
  fun d s ->
  try Hashtbl.find keyword_table s with Not_found -> d

(* to store the position of the beginning of a comment *)
(*let comment_start_pos = ref []*)

(* error reporting *)
open Format

let report_error = function
  | Illegal_character c ->
      Format.printf  "Illegal character (%s)@\n" (Char.escaped c)
  | Unterminated_comment ->
      Format.printf "Comment not terminated@\n"

}


(* ====================================================================== *)

(* translation from Helpers's section in jimple.scc  *)

let  all = _

let  dec_digit = ['0' - '9']
let  dec_nonzero = ['1' - '9']
let  dec_constant = dec_digit+

let  hex_digit = dec_digit | ['a' - 'f'] | ['A' - 'F']
let  hex_constant = '0' ('x' | 'X') hex_digit+

let  oct_digit = ['0' - '7']
let  oct_constant = '0' oct_digit+
	
let  quote = '\''

let  escapable_char = '\\' | ' ' | quote | '.' | '#' | '\"' | 'n' | 't' | 'r' | 'b' | 'f'
let  escape_code = 'u' hex_digit hex_digit hex_digit hex_digit
let  escape_char = '\\' (escapable_char | escape_code)  

let  not_cr_lf = [ ^ '\010' '\013']
let  not_star = [ ^ '*']
let  not_star_slash = [^ '*' '/']

let  alpha_char = ['a' - 'z'] | ['A' - 'Z']
  
let  simple_id_char = alpha_char | dec_digit | '_' | '$'

let  first_id_char = alpha_char | '_' | '$'
  
let  quotable_char = [^ '\010' '\013' '\'']

let  string_char = escape_char | ['\000' - '\033'] | ['\035' - '\091'] | ['\093' - '\127']   

let  line_comment = "//" not_cr_lf*
(*let  long_comment = "/*" not_star* '*'+ (not_star_slash not_star* '*'+)* '/'*)

let  blank = (' ' | '\009')+  
let  ignored_helper = (blank | line_comment)+

let  newline = ('\013' | '\010' | "\010\013")

let full_identifier =
       ((first_id_char | escape_char) (simple_id_char | escape_char)* '.')+  '$'? (first_id_char | escape_char) (simple_id_char | escape_char)*

let identifier = 
      (first_id_char | escape_char) (simple_id_char | escape_char)* | "<clinit>" | "<init>"

(*let identifier =
    (first_id_char | escape_char) (simple_id_char | escape_char)* | '<' (first_id_char | escape_char) (simple_id_char | escape_char)* '>'*)

let quoted_name = quote quotable_char+ quote

let at_identifier = 
  '@' (
    ("parameter" dec_digit+ ':') 
    | "this" ':' 
    | "caughtexception" 
    | "caller") 
	
let integer_constant = (dec_constant | hex_constant | oct_constant) 'L'? 

let float_constant = ((dec_constant '.' dec_constant) (('e'|'E') ('+'|'-')? dec_constant)? ('f'|'F')?)  | ('#' (('-'? "Infinity") | "NaN") ('f' | 'F')? ) 

(* Translation of section Tokens of jimple.scc *)

rule token = parse
  | newline { new_line lexbuf; token lexbuf }
  | "/*" { nest lexbuf; comment lexbuf; token lexbuf } 
  | ignored_helper  { token lexbuf }
  | "," { COMMA }
  | "{" { L_BRACE }
  | "}" { R_BRACE }
  | ";" { SEMICOLON }
  | "[" { L_BRACKET }
  | "]" { R_BRACKET }
  | "(" { L_PAREN }
  | ")" { R_PAREN }
  | ":" { COLON}
  | "." { DOT }
  | "'" { QUOTE }
  | ":=" { COLON_EQUALS }
  | "=" { EQUALS }
  | "&" { AND }
  | "|" { OR }
  | "||" { OROR }
  | "|->" { MAPSTO }
  | "^" { XOR }
  | "%" { MOD }
  | "cmp" { CMP }
  | "cmpl" { CMPL }
  | "cmpg" { CMPG }
  | "==" { CMPEQ }
  | "!=" { CMPNE }
  | ">" { CMPGT }
  | ">=" { CMPGE }
  | "=>" { IMP }
  | "<=>" { BIMP }
  | "<" { CMPLT }
  | "<=" { CMPLE }
  | "<<" { SHL }
  | ">>" { SHR }
  | ">>>" { USHR }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MULT }
  | "-*" { WAND }
  | "/" { DIV }
  | "?" { QUESTIONMARK }
  | "!" { BANG }
  | "|-" { VDASH }
  | "~~>" {LEADSTO}
  | eof { EOF }

  | at_identifier as s { kwd_or_else (AT_IDENTIFIER s) s }
  | full_identifier as s { kwd_or_else (FULL_IDENTIFIER s) s }
  | quoted_name as s { kwd_or_else (QUOTED_NAME s) s }
  | identifier as s { kwd_or_else (IDENTIFIER s) s }

  | integer_constant {
      let s=Lexing.lexeme lexbuf in
      if (String.get s (String.length s -1)) = 'L' then
	 INTEGER_CONSTANT_LONG(int_of_string(String.sub s 0 (String.length s - 1)))
      else 
	 INTEGER_CONSTANT(int_of_string(s))}

  | float_constant   { FLOAT_CONSTANT(float_of_string(Lexing.lexeme lexbuf))}

  | '"' (string_char* as s) '"' { kwd_or_else (STRING_CONSTANT s) s }
  | _ { failwith (error_message (Illegal_character ((Lexing.lexeme lexbuf).[0])) lexbuf)}
and comment = parse 
  | "/*"  { nest lexbuf; comment lexbuf }
  | "*/"  { if unnest lexbuf then comment lexbuf }
  | newline  { new_line lexbuf; comment lexbuf }
  | eof      { failwith (error_message Unterminated_comment lexbuf)}
  | _     { comment lexbuf; }



(* ====================================================================== *)




{ (* trailer *)
}
