(******************************************************************
 JStar: Separation logic verification tool for Java.  
 Copyright (c) 2007-2008,
    Dino Distefano <ddino@dcs.qmul.ac.uk>
    Matthew Parkinson <Matthew.Parkinson@cl.cam.ac.uk>
 All rights reserved. 
*******************************************************************)


{ (* ddino implementation of a lexer for jimple *)
(* header *)
  
open Jparser 

type error =
  | Illegal_character of char
  | Unterminated_comment

exception Error of error * int * int

let incr_linenum lexbuf = 
  let pos = lexbuf.Lexing.lex_curr_p in 
  lexbuf.Lexing.lex_curr_p <- { pos with 
				Lexing.pos_lnum = pos.Lexing.pos_lnum + 1; 
				Lexing.pos_bol = pos.Lexing.pos_cnum; 
			      } 

(* association list of keywords. to be checked *)
let keyword_al = [
   ( "abstract"  , ABSTRACT  );
   ( "final" , FINAL );
   ( "native" , NATIVE );
   ( "public" , PUBLIC );
   ( "protected" , PROTECTED );
   ( "private" , PRIVATE );
   ( "static" , STATIC );
   ( "synchronized" , SYNCHRONIZED );
   ( "transient" , TRANSIENT );
   ( "volatile" , VOLATILE );
   ( "strictfp" , STRICTFP );
   ( "enum" , ENUM );
   ( "annotation"  , ANNOTATION );
   ( "class" , CLASS );
   ( "interface" , INTERFACE );
   ( "void" , VOID );
   ( "boolean" , BOOLEAN );
   ( "byte" , BYTE );
   ( "short" , SHORT );
   ( "char" , CHAR );
   ( "int" , INT );
   ( "long" , LONG );
   ( "float" , FLOAT );
   ( "double" , DOUBLE );
   ( "null_type" , NULL_TYPE );
   ( "unknown" , UNKNOWN );
   ( "extends" , EXTENDS );
   ( "implements" , IMPLEMENTS );
   ( "breakpoint" , BREAKPOINT ); 
   ( "case" , CASE );
   ( "catch" , CATCH );
   ( "goto" , GOTO );
   ( "if" , IF );
   ( "instanceof" , INSTANCEOF  );
   ( "interfaceinvoke" , INTERFACEINVOKE );
   ( "lengthof" , LENGTHOF );
   ( "lookupswitch" , LOOKUPSWITCH );
   ( "new" , NEW );
   ( "newarray" , NEWARRAY );
   ( "newmultiarray" , NEWMULTIARRAY );
   ( "return" , RETURN );
   ( "specialinvoke" , SPECIALINVOKE );
   ( "staticinvoke" , STATICINVOKE );
   ( "tableswitch" , TABLESWITCH );  
   ( "throw" , THROW  );
   ( "throws" , THROWS );
   ( "virtualinvoke" , VIRTUALINVOKE );
   ( "null" , NULL );
   ( "from" , FROM );
   ( "to" , TO );
   ( "with" , WITH );
   ( "cls" , CLS );
   ( "andalso" , ANDALSO );
]


(* to store the position of the beginning of a comment *)
(*let comment_start_pos = ref []*)

(* error reporting *)
open Format

let report_error ppf = function
  | Illegal_character c ->
      fprintf ppf "Illegal character (%s)" (Char.escaped c)
  | Unterminated_comment ->
      fprintf ppf "Comment not terminated"

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

let  escapable_char = '\\' | ' ' | quote | '.' | '#' | '"' | 'n' | 't' | 'r' | 'b' | 'f'
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

let at_identifier = '@' (("parameter" dec_digit+ ':') | "this" ':' | "caughtexception") 
	
let bool_constant =  "true" | "false"  
 
let integer_constant = (dec_constant | hex_constant | oct_constant) 'L'? 

let float_constant = ((dec_constant '.' dec_constant) (('e'|'E') ('+'|'-')? dec_constant)? ('f'|'F')?)  | ('#' (('-'? "Infinity") | "NaN") ('f' | 'F')? ) 

let string_constant = '"' string_char* '"'

(* Translation of section Tokens of jimple.scc *)

rule token = parse
   | newline { incr_linenum lexbuf; token lexbuf }
   | "/*" { comment lexbuf; token lexbuf } 
   | ignored_helper  { token lexbuf }
   | "Abstract"  { ABSTRACT } 
   | "final" { FINAL }
   | "native" { NATIVE }
   | "public" {PUBLIC} 
   | "protected" { PROTECTED }
   | "private" { PRIVATE }
   | "static" { STATIC }
   | "synchronized" { SYNCHRONIZED }
   | "transient" { TRANSIENT }
   | "volatile" { VOLATILE }
   | "strictfp" { STRICTFP }
   | "enum" { ENUM }
   | "annotation"  { ANNOTATION }
   | "class" { CLASS }
   | "interface" { INTERFACE }
   | "void" { VOID }
   | "boolean" { BOOLEAN } 
   | "byte" { BYTE } 
   | "short" { SHORT }
   | "char" { CHAR }
   | "int" { INT }
   | "long" { LONG }
   | "float" { FLOAT }
   | "double" { DOUBLE }
   | "null_type" { NULL_TYPE }
   | "unknown" { UNKNOWN }
   | "extends" { EXTENDS }
   | "implements" { IMPLEMENTS }
   | "breakpoint" { BREAKPOINT } 
   | "case" { CASE }
   | "catch" { CATCH }
   | "cmp" { CMP }
   | "cmpg" { CMPG }
   | "cmpl" { CMPL }
   | "default" { DEFAULT }
   | "entermonitor" { ENTERMONITOR }
   | "exitmonitor" { EXITMONITOR }
   | "goto" { GOTO }
   | "if" { IF }
   | "instanceof" { INSTANCEOF  }
   | "interfaceinvoke" { INTERFACEINVOKE }
   | "lengthof" { LENGTHOF }
   | "lookupswitch" { LOOKUPSWITCH }
   | "neg" { NEG }
   | "new" { NEW }
   | "newarray" { NEWARRAY }
   | "newmultiarray" { NEWMULTIARRAY }
   | "nop" { NOP }
   | "ret" { RET }
   | "return" { RETURN }
   | "specialinvoke" { SPECIALINVOKE }
   | "staticinvoke" { STATICINVOKE }
   | "tableswitch" { TABLESWITCH }  
   | "throw" { THROW  }
   | "throws" { THROWS }
   | "virtualinvoke" { VIRTUALINVOKE }
   | "null" { NULL }
   | "from" { FROM }
   | "to" { TO }
   | "with" { WITH }
   | "cls" { CLS }
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
   | "==" { CMPEQ }
   | "!=" { CMPNE }
   | ">" { CMPGT }
   | ">=" { CMPGE }
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
   | "_" { UNDERSCORE }
   | "?" { QUESTIONMARK }
   | eof { EOF }
   | "listclassfiles" {LISTCLASSFILES} 

   | at_identifier  { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> AT_IDENTIFIER s }

   | full_identifier { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> FULL_IDENTIFIER s } 
   | quoted_name  { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> QUOTED_NAME s }

   | identifier  { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> IDENTIFIER s}

   | bool_constant  { let s = Lexing.lexeme lexbuf in
          try List.assoc s keyword_al
          with Not_found -> BOOL_CONSTANT s }
  
   | integer_constant {
       let s=Lexing.lexeme lexbuf in
       if (String.get s (String.length s -1)) = 'L' then
	 INTEGER_CONSTANT_LONG(int_of_string(String.sub s 0 (String.length s - 1)))
       else 
	 INTEGER_CONSTANT(int_of_string(s))}

   | float_constant   { FLOAT_CONSTANT(float_of_string(Lexing.lexeme lexbuf))}

   | string_constant  { let s = Lexing.lexeme lexbuf in
			let s= String.sub s 1 (String.length s - 2) in 
			try List.assoc s keyword_al
			with Not_found -> STRING_CONSTANT s }

  | _ { raise (Error(Illegal_character ((Lexing.lexeme lexbuf).[0]),
                     Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf)) }
and comment = parse 
  | "/*"  { comment lexbuf; }
  | "*/"  { }
  | newline  { incr_linenum lexbuf; comment lexbuf }
  | eof      { raise (Error(Unterminated_comment,
                     Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))}
  | _     { comment lexbuf; }



(* ====================================================================== *)




{ (* trailer *)
}
