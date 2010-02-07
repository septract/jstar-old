type token =
  | REQUIRES
  | OLD
  | ENSURES
  | AS
  | ABSRULE
  | EQUIV
  | LEADSTO
  | ABSTRACT
  | FINAL
  | NATIVE
  | PUBLIC
  | PROTECTED
  | PRIVATE
  | STATIC
  | SYNCHRONIZED
  | TRANSIENT
  | VOLATILE
  | STRICTFP
  | ENUM
  | ANNOTATION
  | CLASS
  | INTERFACE
  | VOID
  | BOOLEAN
  | BYTE
  | SHORT
  | CHAR
  | INT
  | LONG
  | FLOAT
  | DOUBLE
  | NULL_TYPE
  | UNKNOWN
  | EXTENDS
  | EXPORT
  | IMPLEMENTS
  | BREAKPOINT
  | CASE
  | BANG
  | CATCH
  | CMP
  | CMPG
  | CMPL
  | DEFAULT
  | ENTERMONITOR
  | EXITMONITOR
  | GOTO
  | IF
  | INSTANCEOF
  | INTERFACEINVOKE
  | LENGTHOF
  | LOOKUPSWITCH
  | MAPSTO
  | NEG
  | NEW
  | NEWARRAY
  | NEWMULTIARRAY
  | NOP
  | RET
  | RETURN
  | SPECIALINVOKE
  | STATICINVOKE
  | TABLESWITCH
  | THROW
  | THROWS
  | VIRTUALINVOKE
  | NULL
  | FROM
  | TO
  | WITH
  | CLS
  | COMMA
  | L_BRACE
  | R_BRACE
  | SEMICOLON
  | L_BRACKET
  | R_BRACKET
  | L_PAREN
  | R_PAREN
  | COLON
  | DOT
  | QUOTE
  | INTEGER_CONSTANT of (int)
  | INTEGER_CONSTANT_LONG of (int)
  | FLOAT_CONSTANT of (float)
  | STRING_CONSTANT of (string)
  | QUOTED_NAME of (string)
  | IDENTIFIER of (string)
  | AT_IDENTIFIER of (string)
  | FULL_IDENTIFIER of (string)
  | COLON_EQUALS
  | EQUALS
  | AND
  | OR
  | OROR
  | XOR
  | MOD
  | CMPEQ
  | CMPNE
  | CMPGT
  | CMPGE
  | CMPLT
  | CMPLE
  | SHL
  | SHR
  | USHR
  | PLUS
  | MINUS
  | WAND
  | VDASH
  | MULT
  | DIV
  | UNDERSCORE
  | QUESTIONMARK
  | IMP
  | BIMP
  | EOF
  | ANDALSO
  | DEFINE
  | FALSE
  | TRUE
  | IMPLICATION
  | FRAME
  | ABS
  | INCONSISTENCY
  | RULE
  | PURERULE
  | PRED
  | REWRITERULE
  | EMPRULE
  | WITHOUT
  | WHERE
  | NOTIN
  | NOTINCONTEXT
  | ORTEXT
  | GARBAGE
  | IMPORT
  | INDUCTIVE

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Jimple_global_types.jimple_file
val spec_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Global_types.spec_file
val rule_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Global_types.rules Global_types.importoption list
val question_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Global_types.question list
val test_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Global_types.test list
val inductive_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Global_types.inductive_stmt list
val tactic_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Global_types.tactic_spec
