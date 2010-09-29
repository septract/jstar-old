%{ (* header *)

open VfcAST

let parent_struct = ref ""

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
%token INV

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
array_type: 
 | basic_type L_BRACKET INTEGER_CONSTANT R_BRACKET { Array($1, $3) }
 | struct_type L_BRACKET INTEGER_CONSTANT R_BRACKET { Array($1, $3) }
 | pointer_type L_BRACKET INTEGER_CONSTANT R_BRACKET { Array($1, $3) }
; 
full_type: 
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
 | STRUCT IDENTIFIER L_BRACE fields_decl R_BRACE { if Config.parse_debug() then Printf.printf "struct_decl void %!"; parent_struct := $2; {sname=$2; fields=$4} }
; 
fields_decl: 
 | /* empty */ { [] }
 | full_type IDENTIFIER SEMICOLON fields_decl { 
       let f = { fname = $2; ftype = $1; offset = 0; parent = !parent_struct } 
       in f :: $4
     }
;
fun_decl: 
 | full_type IDENTIFIER L_PAREN var_list R_PAREN stmt
      { if Config.parse_debug() then Printf.printf "fun_decl %!"; {fun_name=$2; ret_type=Some $1; params=$4; body=$6} }
 | VOID IDENTIFIER L_PAREN var_list R_PAREN stmt 
      { if Config.parse_debug() then Printf.printf "fun_decl void %!"; {fun_name=$2; ret_type=None; params=$4; body=$6} }
; 
var_list:
 | /* empty */   { [] }
 | full_type IDENTIFIER { [{vname=$2; vtype=$1; kind=Parameter}] } 
 | full_type IDENTIFIER COMMA var_list { {vname=$2; vtype=$1; kind=Parameter} :: $4 }
;
const:
 | INTEGER_CONSTANT  { Int_const($1) }
 /* todo: BOOLEAN_CONSTANT and NULL_CONSTANT */
; 
exp: 
 | L_PAREN exp R_PAREN  { $2 }
 | const  { Const($1) }
 | IDENTIFIER  { PVar_ref($1) }
 | unop exp  { Prim_op($1, [$2]) } 
 | exp binop exp  { Prim_op($2, [$1; $3] ) }
/* | op L_PAREN exp_list R_PAREN  { Prim_op($1, $3) } */
; 
exp_list: 
 | /* empty */   { [] }
 | exp COMMA exp_list  { $1 :: $3 }
;
op:
 | unop  { $1 }
 | binop  { $1 }
;
unop:
 | BANG  { Neg }
;
/* TODO: handle priorities */
binop: 
 | AND  { And }   
 | OR  { Or }    
 | CMPEQ  { Cmpeq } 
 | CMPNE  { Cmpne } 
 | CMPGT  { Cmpgt } 
 | CMPGE  { Cmpge } 
 | CMPLT  { Cmplt } 
 | CMPLE  { Cmple } 
 | PLUS  { Add } 
 | MINUS { Sub } 
 | STAR { Mult }    
;
stmt: 
 | full_type IDENTIFIER SEMICOLON  { if Config.parse_debug() then Printf.printf "PVar_decl %!"; PVar_decl {vname=$2; vtype=$1; kind=Local} }
 | IDENTIFIER EQUALS exp SEMICOLON  { if Config.parse_debug() then Printf.printf "Assign %!"; Assign($1, $3) }
 | IDENTIFIER EQUALS L_PAREN pointer_type R_PAREN exp SEMICOLON  { if Config.parse_debug() then Printf.printf "Cast %!"; Cast($1, $4, $6) }
 | IDENTIFIER EQUALS exp ARROW IDENTIFIER SEMICOLON  { if Config.parse_debug() then Printf.printf "Heap_read some %!"; Heap_read($1, $3, Some $5) }
 | exp ARROW IDENTIFIER EQUALS exp SEMICOLON  { if Config.parse_debug() then Printf.printf "Heap assn some %!"; Heap_assn($1, Some $3, $5) }
 | IDENTIFIER EQUALS STAR exp SEMICOLON  { if Config.parse_debug() then Printf.printf "Heap_read %!"; Heap_read($1, $4, None) }
 | STAR exp EQUALS exp SEMICOLON  { if Config.parse_debug() then Printf.printf "Heap_assn %!"; Heap_assn($2, None, $4) }
 | SKIP SEMICOLON  { if Config.parse_debug() then Printf.printf "Skip %!"; Skip }
 | IF L_PAREN exp R_PAREN stmt ELSE stmt  { if Config.parse_debug() then Printf.printf "If %!"; If($3, $5, $7) }
 | WHILE L_PAREN exp R_PAREN stmt  { if Config.parse_debug() then Printf.printf "While %!"; While($3, $5) }
 | RETURN SEMICOLON  { if Config.parse_debug() then Printf.printf "Return none %!"; Return(None) }
 | RETURN exp SEMICOLON  { if Config.parse_debug() then Printf.printf "Return some %!"; Return(Some $2) } 
 | IDENTIFIER EQUALS IDENTIFIER L_PAREN exp_list R_PAREN SEMICOLON  { if Config.parse_debug() then Printf.printf "Fun_call %!"; Fun_call($1, $3, $5) }
 | L_BRACE stmt_list R_BRACE  { if Config.parse_debug() then Printf.printf "Block %!"; Block($2) }
 | IDENTIFIER EQUALS ALLOC L_PAREN exp R_PAREN SEMICOLON  { Alloc($1, $5) }
 | FREE L_PAREN exp R_PAREN SEMICOLON  { Free($3) }
 | IDENTIFIER EQUALS FORK L_PAREN IDENTIFIER COLON exp_list R_PAREN SEMICOLON 
    { Fork($1, $5, $7) }
 | JOIN L_PAREN exp R_PAREN SEMICOLON  { Join($3) }
 | GET L_PAREN exp COMMA exp COMMA exp COMMA exp R_PAREN SEMICOLON  { Get($3,$5,$7,$9) }
 | PUT L_PAREN exp COMMA exp COMMA exp COMMA exp R_PAREN SEMICOLON  { Put($3,$5,$7,$9) } 
 | WAIT L_PAREN exp R_PAREN SEMICOLON  { Wait($3) }
 | INV IDENTIFIER  { if Config.parse_debug() then Printf.printf "Inv %!"; Inv($2) }
; 
stmt_list: 
 | stmt  { [$1] }
 | stmt stmt_list  { $1 :: $2 }
