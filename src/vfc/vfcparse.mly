%{ (* header *)

open VfcAST

%} 

%token BYTE
%token INT
%token STRUCT
%token VOID
%token REQUIRES
%token ENSURES
%token SKIP
%token IF
%token ELSE
%token INV
%token RETURN
%token ALLOC
%token FREE
%token FORK
%token JOIN
%token COMMA
%token L_BRACE
%token R_BRACE
%token SEMICOLON
%token L_BRACKET
%token R_BRACKET
%token L_PAREN
%token R_PAREN
%token COLON
%token DOT
%token QUOTE
%token EQUALS
%token PLUS
%token MINUS
%token STAR
%token BANG
%token AND
%token OR
%token CMPEQ
%token CMPNE
%token CMPGT
%token CMPGE
%token CMPLT
%token CMPLE
%token ARROW
%token EOF
%token THREAD 
%token WHILE 
%token GET 
%token PUT
%token WAIT 

%token <int> INTEGER_CONSTANT
%token <string> IDENTIFIER 

%start program             /* the entry point */
%type <VfcAST.vfc_prog> program
%%
program: 
 | EOF { [] }
 | decl program { $1 :: $2 }
;
basic_type: 
 | BYTE { Byte }
 | INT  { Int } 
; 
struct_type: 
 | STRUCT IDENTIFIER { Struct($2) }
; 
pointer_type: 
 | basic_type STAR  { Pointer($1) }
 | struct_type STAR { Pointer($1) }
 | VOID STAR        { Void_ptr }
 | THREAD STAR      { Thread_ptr }
;  
stack_type: 
 | basic_type  { $1 }
 | struct_type { $1 } 
;  
array_type: 
 | stack_type L_BRACKET INTEGER_CONSTANT R_BRACKET { Array($1, $3) }
; 
field_type: 
 | basic_type { $1 }
 | pointer_type { $1 } 
 | struct_type { $1 }
 | array_type { $1 }
; 
decl: 
 | struct_decl { Struct_decl $1 } 
 | fun_decl { Fun_decl $1 }
;
struct_decl: 
 | STRUCT IDENTIFIER L_BRACE fields_decl R_BRACE { {sname=$2; fields=$4} }
; 
fields_decl: 
 | /* empty */ { [] }
 | field_type IDENTIFIER SEMICOLON fields_decl { 
       let f = { fname = $2; ftype = $1; offset = 0 } 
       in f :: $4
     }
;
fun_decl: 
 | stack_type IDENTIFIER L_PAREN var_list R_PAREN L_BRACE stmt R_BRACE 
      { {fun_name=$2; ret_type=Some $1; params=$4; body=Skip} }
 | VOID IDENTIFIER L_PAREN var_list R_PAREN L_BRACE stmt R_BRACE 
      { {fun_name=$2; ret_type=None; params=$4; body=Skip} }
; 
var_list: 
 | stack_type IDENTIFIER { [{vname=$2; vtype=$1; kind=Parameter}] }
 | stack_type IDENTIFIER COMMA var_list { {vname=$2; vtype=$1; kind=Parameter} :: $4 }
;
const:
 | INTEGER_CONSTANT  { Int_const($1) }
 /* todo: BOOLEAN_CONSTANT and NULL_CONSTANT */
; 
exp: 
 | const  { Const($1) }
 | op L_PAREN exp_list R_PAREN  { Prim_op($1, $3) }
 | IDENTIFIER        { PVar_ref($1) }
; 
exp_list: 
 | /* empty */   { [] }
 | exp COMMA exp_list  { $1 :: $3 }
; 
op: 
 | PLUS  { Add } 
 | MINUS { Sub } 
 | STAR  { Mult } 
 | BANG  { Neg }
 | CMPEQ {Cmpeq} 
 | CMPNE {Cmpne} 
 | CMPGT {Cmpgt} 
 | CMPGE {Cmpge} 
 | CMPLT {Cmplt} 
 | CMPLE {Cmple} 
 | AND {And}   
 | OR  {Or}    
; 
stmt: 
 | stack_type IDENTIFIER SEMICOLON  { PVar_decl {vname=$2; vtype=$1; kind=Local} }
 | IDENTIFIER EQUALS exp SEMICOLON  { Assign($1, $3) }
 | IDENTIFIER EQUALS L_PAREN pointer_type R_PAREN exp SEMICOLON  { Cast($1, $4, $6) }
 | IDENTIFIER EQUALS exp ARROW IDENTIFIER SEMICOLON  { Field_read($1, $3, $5) }
 | exp ARROW IDENTIFIER EQUALS exp SEMICOLON  { Field_assn($1, $3, $5) }
 | SKIP SEMICOLON  { Skip }
 | IF L_PAREN exp R_PAREN stmt ELSE stmt SEMICOLON  { If($3, $5, $7) }
 | WHILE L_PAREN exp R_PAREN stmt SEMICOLON  { While($3, $5) }
 | RETURN SEMICOLON  { Return(None) }
 | RETURN exp  { Return(Some $2) } 
 | IDENTIFIER EQUALS IDENTIFIER L_PAREN exp_list R_PAREN SEMICOLON  { Fun_call($1, $3, $5) }
 | L_BRACE stmt_list R_BRACE SEMICOLON  { Block($2) }
 | IDENTIFIER EQUALS ALLOC L_PAREN exp R_PAREN SEMICOLON  { Alloc($1, $5) }
 | FREE L_PAREN exp R_PAREN SEMICOLON  { Free($3) }
 | IDENTIFIER EQUALS FORK L_PAREN IDENTIFIER COLON exp_list R_PAREN SEMICOLON 
    { Fork($1, $5, $7) }
 | JOIN L_PAREN exp R_PAREN SEMICOLON  { Join($3) }
 | GET L_PAREN exp COMMA exp COMMA exp COMMA exp R_PAREN SEMICOLON  { Get($3,$5,$7,$9) }
 | PUT L_PAREN exp COMMA exp COMMA exp COMMA exp R_PAREN SEMICOLON  { Put($3,$5,$7,$9) } 
 | WAIT L_PAREN exp R_PAREN SEMICOLON  { Wait($3) }
; 
stmt_list: 
 | stmt  { [$1] }
 | stmt stmt_list  { $1 :: $2 }
