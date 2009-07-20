/* ddino implementation of a parser for Jimple */

%{ (* header *)
exception Give_up

open Jparsetree

open Vars
open Pterm
open Plogic
open Lexing
open Parsing 
open Specification
open Pprinter

let newPVar x = concretep_str x

let newAnyVar x = AnyVar(0,x)

let newEVar x = EVar(0,x)

let newVar x = if String.get x 0 = '_' then newEVar (String.sub x 1 ((String.length x) -1)) 
    else newPVar x

let location_to_string pos = 
  Printf.sprintf "Line %d character %d" pos.pos_lnum  (pos.pos_cnum - pos.pos_bol + 1)

let parse_error s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Error between %s and %s\n" (location_to_string start_pos) (location_to_string end_pos)

let field_signature2str fs =
  match fs with 
  | Field_signature (c,t,n) ->  mkStrOfFieldSignature c t n
  | _ -> assert false



%} /* declarations */

/* ============================================================= */
/* tokens */

%token ABSTRACT
%token FINAL 
%token NATIVE 
%token PUBLIC 
%token PROTECTED 
%token PRIVATE 
%token STATIC 
%token SYNCHRONIZED 
%token TRANSIENT 
%token VOLATILE 
%token STRICTFP 
%token ENUM 
%token ANNOTATION 
%token CLASS 
%token INTERFACE 
%token VOID 
%token BOOLEAN  
%token BYTE 
%token SHORT 
%token CHAR 
%token INT 
%token LONG 
%token FLOAT 
%token DOUBLE 
%token NULL_TYPE 
%token UNKNOWN 
%token EXTENDS 
%token EXPORT 
%token IMPLEMENTS 
%token BREAKPOINT  
%token CASE 
%token CATCH 
%token CMP 
%token CMPG 
%token CMPL 
%token DEFAULT 
%token ENTERMONITOR 
%token EXITMONITOR 
%token GOTO 
%token IF 
%token INSTANCEOF  
%token INTERFACEINVOKE 
%token LENGTHOF 
%token LOOKUPSWITCH 
%token MAPSTO
%token NEG 
%token NEW 
%token NEWARRAY 
%token NEWMULTIARRAY 
%token NOP 
%token RET 
%token RETURN 
%token SPECIALINVOKE 
%token STATICINVOKE 
%token TABLESWITCH   
%token THROW  
%token THROWS 
%token VIRTUALINVOKE 
%token NULL 
%token FROM 
%token TO 
%token WITH 
%token CLS 
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
%token <int> INTEGER_CONSTANT 
%token <int> INTEGER_CONSTANT_LONG 
%token <float> FLOAT_CONSTANT 
%token <string> STRING_CONSTANT 
%token <string> QUOTED_NAME 
%token <string> IDENTIFIER 
%token <string> AT_IDENTIFIER 
%token <string> FULL_IDENTIFIER 
%token <string> BOOL_CONSTANT
%token COLON_EQUALS 
%token EQUALS 
%token AND 
%token OR 
%token OROR 
%token XOR 
%token MOD 
%token CMPEQ 
%token CMPNE 
%token CMPGT 
%token CMPGE 
%token CMPLT 
%token CMPLE 
%token SHL 
%token SHR 
%token USHR 
%token PLUS 
%token MINUS 
%token WAND
%token MULT 
%token DIV 
%token L_BRACKET 
%token R_BRACKET 
%token UNDERSCORE 
%token QUESTIONMARK 
%token ANDALSO 
%token EOF

%token LISTCLASSFILES 

/* ============================================================= */

%left IDENFIFIER
%left AT_IDENTIFIER
%left QUOTED_NAME
%left FULL_IDENTIFIER




/* entry points */
//%start listing_file
//%type <Jparsetree.list_class_file> listing_file
%start file
%type <Jparsetree.jimple_file> file

%start spec_file
%type <Specification.spec_file> spec_file


%% /* rules */

/* entry points */
file:
   | modifier_list_star file_type class_name extends_clause implements_clause file_body
       {JFile($1, $2, $3, $4, $5, $6)}
;

spec_file:
   | EOF  { [] }
   | classspec spec_file { $1 :: $2 }

classspec: 
   | file_type class_name L_BRACE apf_defines methods_specs R_BRACE  { ($2,$4,$5) }


apf_defines: 
   | apf_define apf_defines { $1 :: $2 }
   | /*empty*/ { [] }

apf_define:
   | identifier L_PAREN lvariable paramlist_question_mark R_PAREN EQUALS formula SEMICOLON  {  let a=match $4 with | Some b -> b | None -> [] in ($1,$3,a,$7,false) }
   | identifier identifier L_PAREN lvariable paramlist_question_mark R_PAREN EQUALS formula SEMICOLON  { let a=match $5 with | Some b -> b | None -> [] in if $1="export" then ($2,$4,a,$8,true) else if $1="define" then ($2,$4,a,$8,false) else assert false }

methods_specs:
   | method_spec methods_specs { $1 :: $2 }
   | /*empty*/ { [] }

spec:
   | L_BRACE formula R_BRACE L_BRACE formula R_BRACE exp_posts  {  {pre=$2;post=$5;excep=$7}  }
   | error { Printf.printf "Was expecting spec of form {form} {form}\n"; raise Parse_error }
specs:
   | spec ANDALSO specs  { $1 :: $3 }
   | spec     {[$1]}
   | error ANDALSO specs { raise Parse_error }

method_spec:
   | method_signature_short COLON specs  SEMICOLON  { Dynamic($1, $3) }
   | STATIC method_signature_short COLON specs SEMICOLON  { Static($2, $4) }
   | method_signature_short COLON specs   { Dynamic($1, $3) }
   | STATIC method_signature_short COLON specs  { Static($2, $4) }

exp_posts:
   | L_BRACE class_name COLON formula R_BRACE exp_posts { ClassMap.add $2 $4 $6 }
   | /*empty */ { ClassMap.empty }

modifier:
   | ABSTRACT      {Abstract} 
   | FINAL         {Final} 
   | NATIVE        {Native}
   | PUBLIC        {Public}
   | PROTECTED     {Protected}
   | PRIVATE       {Private}
   | STATIC        {Jparsetree.Static}
   | SYNCHRONIZED  {Synchronized}
   | TRANSIENT     {Transient}
   | VOLATILE      {Volatile}
   | STRICTFP      {Strictfp}
   | ENUM          {Enum}
   | ANNOTATION    {Annotation}
;
file_type:
   | CLASS  { ClassFile }
   | INTERFACE { InterfaceFile }
;
extends_clause:
   | EXTENDS class_name {Some $2}
   | /* empty */ {None}
;
implements_clause:
   | IMPLEMENTS class_name_list {Some $2}
   | /* empty */ { None }
;
file_body:
   | L_BRACE member_list_star R_BRACE {$2}
;
class_name_list:
   | class_name { [$1] } 
   | class_name COMMA class_name_list {$1::$3}
;
modifier_list_star:
   | /* empty */ { [] } 
   | modifier  modifier_list_star {$1::$2}
;
member_list_star:
   | /* empty */ { [] } 
   | member  member_list_star {$1::$2}
;
member:
   | modifier_list_star jtype name SEMICOLON {Field($1,$2,$3)}
   | modifier_list_star jtype name L_PAREN parameter_list_question_mark R_PAREN throws_clause method_body {Method($1,$2,$3,$5,$7,$8)}
;
jtype:
   | VOID {Void}
   | nonvoid_type {Non_void($1)} 
;
parameter_list:
   | parameter { [$1] }
   | parameter COMMA parameter_list { $1::$3 }
;
parameter:
   | nonvoid_type {$1}
;
throws_clause:
   | THROWS class_name_list { Some $2 };
   | /* empty */ { None }
;
base_type_no_name:
   | BOOLEAN {Boolean}  
   | BYTE {Byte}     
   | CHAR {Char}     
   | SHORT {Short}   
   | INT {Int}      
   | LONG {Long}    
   | FLOAT {Float}  
   | DOUBLE {Double} 
   | NULL {Null_type}
;
base_type:
   | base_type_no_name {$1}
   | class_name {Class_name $1}
;
integer_constant:
   | INTEGER_CONSTANT { $1 } 
;
integer_constant_long:
   | INTEGER_CONSTANT_LONG { $1 } 
;
float_constant:
   | FLOAT_CONSTANT { $1 } 
;
string_constant:
   | STRING_CONSTANT { $1 } 
;
quoted_name:
   | QUOTED_NAME { $1 }
;
identifier:
   | IDENTIFIER { $1 }
;
at_identifier:
   | AT_IDENTIFIER { $1 }
;
full_identifier:
   | FULL_IDENTIFIER { $1 }
;
bool_constant:
   | BOOL_CONSTANT { $1 }
;
nonvoid_type:
   | base_type_no_name array_brackets_list_star  {Base($1,$2)}
   | quoted_name array_brackets_list_star {Quoted($1,$2)}
   | identifier array_brackets_list_star {Ident_NVT($1,$2)}
   | full_identifier array_brackets_list_star {Full_ident_NVT($1,$2)}
;
/* ddino: dunno what to do with this array_brackets. this in any case does not typr check */
array_brackets_list_star:
   | /* empty */ { [] }
   | L_BRACKET R_BRACKET array_brackets_list_star { "[]"::$3 }
;
method_body:
   | SEMICOLON {None}
   | L_BRACE declaration_or_statement_list_star catch_clause_list_star R_BRACE  {Some($2,$3)}
;
declaration_or_statement:
   | declaration { DOS_dec($1) }
   | statement { DOS_stm($1) }
;
declaration_or_statement_list_star:
   | /* empty */ { [] } 
   | declaration_or_statement  declaration_or_statement_list_star {$1::$2}
;
declaration:
   | jimple_type local_name_list SEMICOLON {Declaration($1,$2)}
;
catch_clause_list_star:
   | /* empty */ { [] } 
   | catch_clause  catch_clause_list_star {$1::$2}
;
jimple_type:
   | UNKNOWN {None} 
   | nonvoid_type {Some(Non_void($1))}
   | NULL_TYPE {None}
;
local_name:
   | name {$1}
;
local_name_list:
   | local_name { [$1] }
   | local_name COMMA local_name_list { $1::$3 }
;
case_stmt_list_plus:
   | case_stmt { [$1] }
   | case_stmt case_stmt_list_plus { $1::$2 }
;
statement:
   | label_name COLON  {Label_stmt($1)}            
   | BREAKPOINT SEMICOLON  {Breakpoint_stmt}   
   | ENTERMONITOR immediate SEMICOLON {Entermonitor_stmt($2)} 
   | EXITMONITOR immediate SEMICOLON  {Exitmonitor_stmt($2)}  
   | TABLESWITCH L_PAREN immediate R_PAREN L_BRACE case_stmt_list_plus R_BRACE SEMICOLON {Tableswitch_stmt($3,$6)}  
   | LOOKUPSWITCH L_PAREN immediate R_PAREN L_BRACE case_stmt_list_plus R_BRACE SEMICOLON {Lookupswitch_stmt($3,$6)} 
   | local_name COLON_EQUALS at_identifier SEMICOLON {Identity_no_type_stmt($1,$3)}  
   | local_name COLON_EQUALS at_identifier jtype SEMICOLON  {Identity_stmt($1,$3,$4)}     
   | variable EQUALS expression SEMICOLON  {Assign_stmt($1,$3)}       
   | IF bool_expr goto_stmt     {If_stmt($2,$3)}           
   | goto_stmt {Goto_stmt($1)}         
   | NOP SEMICOLON     {Nop_stmt}          
   | RET immediate_question_mark SEMICOLON     {Ret_stmt($2)}          
   | RETURN immediate_question_mark SEMICOLON  {Return_stmt($2)}       
   | THROW immediate SEMICOLON     {Throw_stmt($2)}        
   | invoke_expr SEMICOLON     {Invoke_stmt($1)}       
;
immediate_question_mark:
   | immediate {Some $1}
   | /* empty */ { None }
;
label_name:
   |identifier {$1}
;
case_stmt:
   |case_label COLON goto_stmt {Case_stmt($1,$3)}
;
minus_question_mark:
   | MINUS { Negative }
   | /* emtpy */  { Positive }
;
case_label:
   | CASE minus_question_mark integer_constant  {Case_label($2,$3)} 
   | DEFAULT     {Case_label_default}  
;
goto_stmt:
   | GOTO label_name SEMICOLON {$2}
;
catch_clause:
   | CATCH class_name FROM label_name TO label_name WITH label_name SEMICOLON {Catch_clause($2,$4,$6,$8)}
;
expression:
   | new_expr   {$1}         
   | L_PAREN nonvoid_type R_PAREN immediate {Cast_exp($2,$4)}        
   | immediate INSTANCEOF nonvoid_type  {Instanceof_exp($1,$3)}  
   | invoke_expr     {Invoke_exp $1}      
   | reference {Reference_exp $1}
   | binop_expr {$1}
   | unop_expr {$1}
   | immediate {Immediate_exp $1}   
;
new_expr:
   | NEW base_type  {New_simple_exp($2)} 
   | NEWARRAY L_PAREN  nonvoid_type R_PAREN  fixed_array_descriptor {New_array_exp($3,$5)}  
   | NEWMULTIARRAY  L_PAREN base_type R_PAREN array_descriptor_list_plus  {New_multiarray_exp($3,$5)}  
;
array_descriptor_list_plus:
   | array_descriptor { [$1] }
   | array_descriptor array_descriptor_list_plus { $1::$2 }
;
array_descriptor:
  L_BRACKET immediate_question_mark R_BRACKET { $2 }
;
variable:
   |reference {Var_ref($1)}
   |local_name {Var_name($1)}
;
bool_expr:
   |binop_expr     {$1} 
   |unop_expr    {$1}  
;
arg_list_question_mark:
   | arg_list { Some $1 }
   | /* empty */ { None }
;
invoke_expr:
   |nonstatic_invoke local_name DOT method_signature L_PAREN arg_list_question_mark R_PAREN 
       {Invoke_nostatic_exp($1,$2,$4,$6)}
   |STATICINVOKE method_signature L_PAREN  arg_list_question_mark R_PAREN  
       {Invoke_static_exp($2,$4)}    
;
binop_expr:
   |immediate binop immediate {Binop_exp($2,$1,$3)}
;
unop_expr:
   | unop immediate {Unop_exp($1,$2)}
;
nonstatic_invoke:  
   | SPECIALINVOKE      {Special_invoke}   
   | VIRTUALINVOKE      {Virtual_invoke}   
   | INTERFACEINVOKE    {Interface_invoke} 
;
parameter_list_question_mark:
   | parameter_list { Some $1 }
   | /* empty */ { None }
;
method_signature:
   | CMPLT class_name COLON jtype name L_PAREN parameter_list_question_mark R_PAREN CMPGT
       {Method_signature($2,$4,$5,$7)}
;
method_signature_short:
   | jtype name L_PAREN parameter_list_question_mark R_PAREN
       { ($1,$2,$4) }
;
reference:
   |array_ref  {$1} 
   |field_ref  {$1} 
;
array_ref:
  identifier fixed_array_descriptor {Array_ref($1,$2)}
;
field_ref:
   |local_name DOT field_signature     { Field_local_ref($1,$3)} 
   |field_signature {Field_sig_ref($1)}   
;
field_signature:
    CMPLT class_name COLON jtype name CMPGT  {Field_signature($2,$4,$5)}
;
fixed_array_descriptor:
   L_BRACKET immediate R_BRACKET {$2}
;
arg_list:
   | immediate { [$1] }
   | immediate COMMA arg_list { $1::$3 }
;
immediate:
   |local_name     { Immediate_local_name($1) }    
   |constant    { Immediate_constant($1) } 
;
constant:
   | minus_question_mark integer_constant {Int_const($1,$2)} 
   | minus_question_mark integer_constant_long {Int_const_long($1,$2)} 
   | minus_question_mark  float_constant  {Float_const($1,$2)}
   | string_constant     {String_const($1)}  
   | CLASS string_constant {Clzz_const($2)}    
   | NULL {Null_const}    
;
binop:
   | AND {And}   
   | OR  {Jparsetree.Or}    
   | XOR {Xor}   
   | MOD {Mod}   
   | CMP {Cmp}   
   | CMPG {Cmpg}  
   | CMPL {Cmpl}  
   | CMPEQ {Cmpeq} 
   | CMPNE {Cmpne} 
   | CMPGT {Cmpgt} 
   | CMPGE {Cmpge} 
   | CMPLT {Cmplt} 
   | CMPLE {Cmple}   
   | SHL {Shl}   
   | SHR {Shr}   
   | USHR {Ushr}  
   | PLUS {Plus}  
   | MINUS {Minus} 
   | MULT {Mult}  
   | DIV {Div}   
;
unop:
   | LENGTHOF   {Lengthof} 
   | NEG {Neg}
;
class_name:
   | quoted_name     {Quoted_clname $1} 
   | identifier {Identifier_clname $1}
   | full_identifier {Full_identifier_clname $1}
;
name:
   | quoted_name {Quoted_name $1}
   | identifier {Identifier_name $1}
;



lvariable:
   | at_identifier { newPVar($1) }
   | identifier { newVar($1) }
   | QUESTIONMARK identifier { newAnyVar($2) }
;
fldlist: 
   | identifier EQUALS argument { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUALS argument SEMICOLON fldlist  { ($1,$3) :: $5 }
;
paramlist_question_mark:
   | COMMA L_BRACE paramlist R_BRACE { Some $3 }
   | COMMA paramlist { Some $2 }
   | /* empty */ { None }
;
paramlist: 
   | identifier EQUALS lvariable { [($1,Arg_var $3)] }
   | /*empty*/ { [] }
   | identifier EQUALS lvariable SEMICOLON fldlist  { ($1,Arg_var $3) :: $5 }
;
argument:
   | lvariable {Arg_var ($1)}
   | identifier L_PAREN argument_list R_PAREN {Arg_op($1,$3) }        
   | INTEGER_CONSTANT {Arg_string(string_of_int $1)} 
   | STRING_CONSTANT {Arg_string($1)} 
   | field_signature {Arg_string(field_signature2str $1)}
   | L_BRACE fldlist R_BRACE {mkArgRecord $2}
;

argument_list_ne:
   | argument {$1::[]}
   | argument COMMA argument_list_ne { $1::$3 }
argument_list:
   | /*empty*/  {[]}
   | argument_list_ne {$1}
;



pure: 
   | identifier L_PAREN argument_list R_PAREN {[P_PPred($1,$3)] }
   | argument EQUALS argument { mkEQ($1,$3) }
   | argument CMPNE argument { mkNEQ($1,$3) }
   | argument COLON identifier { [P_PPred("type", [$1;Arg_string($3)])] }
;
pure_list:
   |      { [] }
   | pure { $1 }
   | pure MULT pure_list {pconjunction $1 $3}
;
combine: 
   | formula OROR formula  { mkOr($1,$3) }
   | formula WAND formula  { mkWand($1,$3) }
spatial:
   | argument DOT field_signature MAPSTO  argument { [P_SPred("field", [$1; Arg_string(field_signature2str $3); $5] )] }
   | identifier L_PAREN argument_list R_PAREN {if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)] }
   | full_identifier L_PAREN argument_list R_PAREN {if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)] }
   | L_PAREN combine R_PAREN { $2 }
/*   | FALSE {False}*/
;
spatial_list:
   |      { [] }
   | spatial { $1 }
   | spatial MULT spatial_list {pconjunction $1 $3} 
;
formula:
   | pure_list OR spatial_list { pconjunction $1 $3 }
;


%% (* trailer *)
