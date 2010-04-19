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
      Printf.sprintf "Illegal character %c  found at line %d character %d.\n" 
	c 
	lb.lex_curr_p.pos_lnum 
	(lb.lex_curr_p.pos_cnum - lb.lex_curr_p.pos_bol)
  | Unterminated_comment -> Printf.sprintf "Unterminatated comment started at line %d character %d in %s.\n"
	!nest_start_pos.pos_lnum 
	(!nest_start_pos.pos_cnum  - !nest_start_pos.pos_bol)
	lb.lex_curr_p.pos_fname



(* association list of keywords. to be checked *)
let keyword_al = [
   ( "requires" , REQUIRES );
   ( "old" , OLD );
   ( "ensures" , ENSURES );
   ( "abstract"  , ABSTRACT  );
   ( "as"  , AS  );
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
   ( "export" , EXPORT );
   ( "exports" , EXPORTS );
   ( "axioms" , AXIOMS );
   ( "define" , DEFINE );
  ("import",IMPORT);
  ("False",FALSE);
  ("True",TRUE);
  ("Emp",EMP);
  ("Implication",IMPLICATION);
  ("Frame",FRAME);
  ("Garbage",GARBAGE);
  ("Inconsistency",INCONSISTENCY);
  ("rule",RULE);
  ("rewrite",REWRITERULE);
  ("emprule",EMPRULE);
  ("purerule",PURERULE);
  ("if",IF);
  ("without",WITHOUT);  
  ("notin",NOTIN);  
  ("notincontext",NOTINCONTEXT);  
  ("where",WHERE);
  ("or",ORTEXT);
  ("abstraction",ABSRULE);
  ("equiv",EQUIV);
  ("inductive" , INDUCTIVE );
  ("nop",NOOP);
  ("label",LABEL);
  ("end",END);
  ("assign",ASSIGN)
]




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

let at_identifier = '@' (("parameter" dec_digit+ ':') | "this" ':' | "caughtexception") 
	
let integer_constant = (dec_constant | hex_constant | oct_constant) 'L'? 

let float_constant = ((dec_constant '.' dec_constant) (('e'|'E') ('+'|'-')? dec_constant)? ('f'|'F')?)  | ('#' (('-'? "Infinity") | "NaN") ('f' | 'F')? ) 

let string_constant = '"' string_char* '"'

let core_label = (first_id_char | escape_char) (simple_id_char | escape_char)* | "<clinit>" | "<init>"

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
			
  | _ { raise (Failure (error_message (Illegal_character ((Lexing.lexeme lexbuf).[0])) lexbuf))}
and comment = parse 
  | "/*"  { nest lexbuf; comment lexbuf }
  | "*/"  { if unnest lexbuf then comment lexbuf }
  | newline  { new_line lexbuf; comment lexbuf }
  | eof      { raise (Failure (error_message Unterminated_comment lexbuf))}
  | _     { comment lexbuf; }



(* ====================================================================== *)




{ (* trailer *)
}
