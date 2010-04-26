/********************************************************
   This file is part of jStar 
	src/parsing/jparser.mly
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************/
/* ddino implementation of a parser for Jimple */

%{ (* header *)
exception Give_up

open Jparsetree

open Vars
open Lexing
open Parsing 
open Jimple_global_types
open Spec
open Load
open Spec_def
open Psyntax


let newPVar x = concretep_str x

let newAnyVar x = AnyVar(0,x)

let newEVar x = EVar(0,x)

let newVar x = 
  if x = "_" then freshe() 
  else if String.get x 0 = '_' then newEVar (String.sub x 1 ((String.length x) -1)) 
  else newPVar x


let msig_simp (mods,typ,name,args_list) =
  let args_list = List.map fst args_list in
  (mods,typ,name,args_list) 

let bind_spec_vars (mods,typ,name,args_list) {pre=pre;post=post;excep=excep} =
  (* Make substitution to normalise names *)
  let subst = Psyntax.empty in 
  let subst = Psyntax.add (newPVar("this")) (Arg_var(Support_syntax.this_var)) subst in 
  (* For each name that is given convert to normalised param name*)
  let _,subst = 
    List.fold_left 
      (fun (n,subst) arg_opt -> 
	(n+1,
	 match arg_opt with 
	   ty,None -> subst 
	 | ty,Some str -> 
	     Psyntax.add 
	       (newPVar(str)) 
	       (Arg_var(Support_syntax.parameter_var n)) 
	       subst
	)) 
	  (0,subst) args_list in

  {pre=subst_pform subst pre;
   post=subst_pform subst post;
   excep=ClassMap.map (subst_pform subst) excep}

let mkDynamic (msig, specs) =
  let specs = List.map (bind_spec_vars msig) specs in 
  let msig = msig_simp msig in   
  Dynamic(msig,specs)

let mkStatic (msig, specs) =
  let specs = List.map (bind_spec_vars msig) specs in 
  let msig = msig_simp msig in   
  Static(msig,specs)
  
    
  

let location_to_string pos = 
  Printf.sprintf "Line %d character %d" pos.pos_lnum  (pos.pos_cnum - pos.pos_bol + 1)

let parse_error s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Error between %s and %s\n%s\n" (location_to_string start_pos) (location_to_string end_pos) s

let parse_warning s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Warning %s (between %s and %s)\n" s (location_to_string start_pos) (location_to_string end_pos)

let field_signature2str fs =
  match fs with 
  | Field_signature (c,t,n) ->  Pprinter.mkStrOfFieldSignature c t n
  | _ -> assert false


%} /* declarations */

/* ============================================================= */
/* tokens */
%token REQUIRES
%token OLD
%token ENSURES
%token AS
%token ABSRULE
%token EQUIV
%token LEADSTO
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
%token EXPORTS
%token AXIOMS
%token IMPLEMENTS 
%token BREAKPOINT  
%token CASE 
%token BANG
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
%token VDASH
%token DASHV
%token MULT 
%token DIV 
%token L_BRACKET 
%token R_BRACKET 
%token UNDERSCORE 
%token QUESTIONMARK 
%token IMP
%token BIMP


%token EOF


%token ANDALSO 
%token DEFINE

%token FALSE
%token TRUE
%token IMPLICATION
%token FRAME
%token ABS
%token ABDUCTION
%token INCONSISTENCY
%token RULE
%token PURERULE
%token PRED
%token REWRITERULE
%token EMPRULE
%token IF
%token WITHOUT
%token WHERE
%token NOTIN
%token NOTINCONTEXT
%token ORTEXT
%token GARBAGE
%token IMPORT 

%token INDUCTIVE


/* ============================================================= */

%left IDENFIFIER
%left AT_IDENTIFIER
%left QUOTED_NAME
%left FULL_IDENTIFIER

%left OR
%left OROR
%left MULT
%left AND
%left XOR 
%left MOD
%left CMP 
%left CMPG 
%left CMPL 
%left CMPEQ 
%left CMPNE
%left CMPGT
%left CMPGE
%left CMPLT
%left CMPLE
%left SHL 
%left SHR 
%left USHR 
%left PLUS
%left MINUS 
%left DIV


%left DEFINE
%left EXPORT


/* entry points */
//%start listing_file
//%type <Jparsetree.list_class_file> listing_file
%start file
%type <Jimple_global_types.jimple_file> file

%start spec_file
%type <Spec_def.class_spec Load.importoption list> spec_file

%start rule_file
%type <Psyntax.rules Load.importoption list> rule_file


%start question_file
%type <Psyntax.question list> question_file

%start test_file
%type <Psyntax.test list> test_file

%start inductive_file
%type <Psyntax.inductive_stmt list> inductive_file

%% /* rules */

file:
   | modifier_list_star file_type class_name extends_clause implements_clause file_body
       {JFile($1, $2, $3, $4, $5, $6)}
;

spec_file:
   | EOF  { [] }
   | IMPORT  STRING_CONSTANT  SEMICOLON spec_file{ (ImportEntry $2) :: $4 }
   | classspec spec_file { (NormalEntry $1) :: $2 }

classspec: 
   | file_type class_name extends_clause implements_clause L_BRACE apf_defines exports_clause axioms_clause methods_specs R_BRACE  { {class_or_interface=$1;classname=$2;extends=$3;implements=$4;apf=$6;exports=$7;axioms=$8;methodspecs=$9} }


apf_defines: 
   | apf_define apf_defines { $1 :: $2 }
   | /*empty*/ { [] }

eq_as: 
   | EQUALS { (* Deprecated *)}
   | AS {}

apf_define:
   | EXPORT identifier L_PAREN lvariable paramlist_question_mark R_PAREN eq_as formula SEMICOLON  
       { let a=match $5 with | Some b -> b | None -> [] in ($2,$4,a,$8,true) }
   | DEFINE identifier L_PAREN lvariable paramlist_question_mark R_PAREN eq_as formula SEMICOLON  
       { let a=match $5 with | Some b -> b | None -> [] in ($2,$4,a,$8,false) }
			
exports_clause:
   | EXPORTS L_BRACE named_implication_star R_BRACE WHERE L_BRACE exportLocal_predicate_def_star R_BRACE { Some ($3,$7) }
	 | /*empty*/ {None}

axioms_clause:
	 | AXIOMS L_BRACE named_implication_star R_BRACE { Some $3 }
	 | /*empty*/ {None}

named_implication_star:
   | named_implication named_implication_star { $1 @ $2 }
   | /*empty*/ { [] }

named_implication:
   | identifier COLON formula IMP formula SEMICOLON { [($1,$3,$5)] }
   | identifier COLON formula BIMP formula SEMICOLON { [($1^"_forwards",$3,$5); ($1^"_backwards",$5,$3)] }

exportLocal_predicate_def_star:
   | exportLocal_predicate_def exportLocal_predicate_def_star { $1 :: $2 }
   | /*empty*/ { [] }

exportLocal_predicate_def:
   | identifier L_PAREN lvariable_list_ne R_PAREN eq_as formula SEMICOLON { ($1,$3,$6) }

methods_specs:
   | method_spec methods_specs { $1 :: $2 }
   | /*empty*/ { [] }

spec:
   | L_BRACE formula R_BRACE L_BRACE formula R_BRACE exp_posts  {  {pre=$2;post=$5;excep=$7}  }
specs:
   | spec ANDALSO specs  { $1 :: $3 }
   | spec     {[$1]}

method_spec:
   | method_signature_short COLON specs  SEMICOLON  { mkDynamic($1, $3) }
   | method_signature_short STATIC COLON specs SEMICOLON  { mkStatic($1, $4) }
   | method_signature_short COLON specs   { mkDynamic($1, $3) }
   | method_signature_short STATIC COLON specs  { mkStatic($1, $4) }

exp_posts:
   | L_BRACE identifier COLON formula R_BRACE exp_posts { ClassMap.add $2 $4 $6 }
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
       
extends_clause:
   | EXTENDS class_name_list { $2 } /* stephan mult inh */ 
   | /* empty */ { [] }
;
implements_clause:
   | IMPLEMENTS class_name_list { $2 }
   | /* empty */ { [] }
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
   | modifier_list_star jtype name L_PAREN parameter_list_question_mark R_PAREN
   throws_clause requires_clause old_clauses ensures_clause method_body
   {Method($1,$2,$3,$5,$7,$8,$9,$10,$11)}
;
jtype:
   | VOID {Void}
   | nonvoid_type {Non_void($1)} 
;
parameter_list:
   | parameter { [$1] }
   | parameter COMMA parameter_list { $1::$3 }
;
parameter_list_args_opt:
   | parameter_args_opt { [$1] }
   | parameter_args_opt COMMA parameter_list_args_opt { $1::$3 }
;
parameter:
   | nonvoid_type {$1}
;
parameter_args_opt:
   | nonvoid_type {$1,None}
   | nonvoid_type identifier {$1,Some $2}
;
throws_clause:
   | THROWS class_name_list { Some $2 }
   | /* empty */ { None }
;
requires_clause:
   | REQUIRES method_body { $2 }
   | /* empty */ { None }
;
old_clauses:
   | old_clause old_clauses { $1::$2 }
   | /* empty */ { [] }
;
old_clause:
   | OLD method_body { $2 }
;
ensures_clause:
   | ENSURES method_body { $2 }
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
   | AS { "as" }
   | IDENTIFIER { $1 }
/*   | DEFINE     { "define" }
   | EXPORT     { "export" }
   | ANDALSO    { "andalso" }*/
  | FALSE   { "False" }
  | TRUE   { "True" }
  | GARBAGE   { "Garbage" }
/*  | IMPLICATION   { "Implication" }
  | FRAME   { "Frame" }
  | INCONSISTENCY   { "Inconsistency" }*/
/*  | RULE   { "rule" }
  | EMPRULE   { "emprule" }
  | PURERULE   { "purerule" }
  | WITHOUT   { "without" }  
  | NOTIN   { "notin" }  
  | NOTINCONTEXT   { "notincontext" }  
  | WHERE   { "where" }*/
/*  | ORTEXT   { "or" }*/
/*  | ABSRULE   { "abstraction" }*/
;
at_identifier:
   | AT_IDENTIFIER { $1 }
;
full_identifier:
   | FULL_IDENTIFIER { $1 }
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
	 | L_BRACE lvariable_list R_BRACE COLON spec SEMICOLON {Spec_stmt($2,$5)}
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
variable_list:
	 | /*empty*/  {[]}
	 | variable variable_list { $1 :: $2 } 
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
   | arg_list { $1 }
   | /* empty */ { [] }
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
   | parameter_list { $1 }
   | /* empty */ { [] }
;
parameter_args_opt_list_question_mark:
   | parameter_list_args_opt { $1 }
   | /* empty */ { [] }
;
method_signature:
   | CMPLT class_name COLON jtype name L_PAREN parameter_list_question_mark R_PAREN CMPGT
       {Method_signature($2,$4,$5,$7)}
;
method_signature_short:
   | modifier_list_star jtype name L_PAREN parameter_args_opt_list_question_mark R_PAREN
       { $1,$2,$3,$5 }
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
binop_no_mult:
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
   | DIV {Div}   
;
binop_val_no_multor:
   | AND {And}   
   | XOR {Xor}   
   | MOD {Mod}   
   | SHL {Shl}   
   | SHR {Shr}   
   | USHR {Ushr}  
   | PLUS {Plus}  
   | MINUS {Minus} 
   | DIV {Div}   
//   | OR  {Jparsetree.Or}    
;
binop_val:
   | OR  {Jparsetree.Or}    
   | MULT {Mult}
   | binop_val_no_multor {$1}
;
binop_cmp:
   | CMP {Cmp}   
   | CMPG {Cmpg}  
   | CMPL {Cmpl}  
   | CMPEQ {Cmpeq} 
   | CMPNE {Cmpne} 
   | CMPGT {Cmpgt} 
   | CMPGE {Cmpge} 
   | CMPLT {Cmplt} 
   | CMPLE {Cmple}   
;
binop: 
   |  binop_no_mult { $1 } 
   |  MULT { Mult }
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

lvariable_list_ne:
   |  lvariable    { [$1] }
   |  lvariable COMMA lvariable_list_ne  { $1 :: $3 }

lvariable_list:
   |  {[]}
   | lvariable_list_ne { $1 }
;

lvariable_npv:
   | at_identifier { newPVar($1) }
   | identifier { newVar($1) }
;

lvariable_list_ne_npv:
   |  lvariable_npv    { [$1] }
   |  lvariable_npv COMMA lvariable_list_ne_npv  { $1 :: $3 }

lvariable_list_npv:
   |  {[]}
   | lvariable_list_ne_npv { $1 }
;

fldlist: 
   | identifier EQUALS jargument { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUALS jargument SEMICOLON fldlist  { ($1,$3) :: $5 }
;

fldlist_npv: 
   | identifier EQUALS jargument_npv { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUALS jargument_npv SEMICOLON fldlist_npv  { ($1,$3) :: $5 }
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


/* Code for matching where not allowing question mark variables:
   no pattern vars*/
jargument_npv:
   | RETURN { Arg_var (newPVar(Support_syntax.name_ret_var)) }
   | lvariable_npv {Arg_var ($1)}
   | identifier L_PAREN jargument_list_npv R_PAREN {Arg_op($1,$3) }        
   | INTEGER_CONSTANT {Arg_string(string_of_int $1)} 
   | MINUS INTEGER_CONSTANT {Arg_string("-" ^(string_of_int $2))}
   | STRING_CONSTANT {Arg_string($1)} 
   | field_signature {Arg_string(field_signature2str $1)}
   | L_BRACE fldlist_npv R_BRACE {mkArgRecord $2}
   | L_PAREN jargument_npv binop_val_no_multor jargument_npv R_PAREN { Arg_op(Support_syntax.bop_to_prover_arg $3, [$2;$4]) }
;

jargument_list_ne_npv:
   | jargument_npv {$1::[]}
   | jargument_npv COMMA jargument_list_ne_npv { $1::$3 }
jargument_list_npv:
   | /*empty*/  {[]}
   | jargument_list_ne_npv {$1}
;



jargument:
   | RETURN { Arg_var (newPVar(Support_syntax.name_ret_var)) }
   | lvariable {Arg_var ($1)}
   | identifier L_PAREN jargument_list R_PAREN {Arg_op($1,$3) }        
   | INTEGER_CONSTANT {Arg_string(string_of_int $1)} 
   | MINUS INTEGER_CONSTANT {Arg_string("-" ^(string_of_int $2))}
   | STRING_CONSTANT {Arg_string($1)} 
   | field_signature {Arg_string(field_signature2str $1)}
   | L_BRACE fldlist R_BRACE {mkArgRecord $2}
   | L_PAREN jargument binop_val_no_multor jargument R_PAREN { Arg_op(Support_syntax.bop_to_prover_arg $3, [$2;$4]) }
;

jargument_list_ne:
   | jargument {$1::[]}
   | jargument COMMA jargument_list_ne { $1::$3 }
jargument_list:
   | /*empty*/  {[]}
   | jargument_list_ne {$1}
;


  
formula: 
   |  { [] }
   | FALSE { mkFalse}
   | GARBAGE { mkGarbage}
   | lvariable DOT jargument MAPSTO  jargument { [P_SPred("field", [Arg_var $1; $3; $5] )] }
   | BANG identifier L_PAREN jargument_list R_PAREN { [P_PPred($2, $4)] } 
   | identifier L_PAREN jargument_list R_PAREN 
       {if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)] }
   | full_identifier L_PAREN jargument_list R_PAREN {if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)] }
   | formula MULT formula { pconjunction $1 $3 }
   | formula OR formula { if Config.symb_debug() then parse_warning "deprecated use of |"  ; pconjunction (purify $1) $3 }
   | formula OROR formula { mkOr ($1,$3) }
   | lvariable COLON identifier { [P_PPred("type", [Arg_var($1);Arg_string($3)])] }
   | jargument binop_cmp jargument { Support_syntax.bop_to_prover_pred $2 $1 $3 }
   | jargument EQUALS jargument { Support_syntax.bop_to_prover_pred (Cmpeq) $1 $3 }
   | L_PAREN formula R_PAREN { $2 }

formula_npv: 
   |  { [] }
   | FALSE { mkFalse}
   | GARBAGE { mkGarbage}
   | lvariable_npv DOT jargument_npv MAPSTO  jargument_npv { [P_SPred("field", [Arg_var $1; $3; $5] )] }
   | BANG identifier L_PAREN jargument_list_npv R_PAREN { [P_PPred($2, $4)] } 
   | identifier L_PAREN jargument_list_npv R_PAREN 
       {if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)] }
   | full_identifier L_PAREN jargument_list_npv R_PAREN {if List.length $3 =1 then [P_SPred($1,$3 @ [mkArgRecord []])] else [P_SPred($1,$3)] }
   | formula_npv MULT formula_npv { pconjunction $1 $3 }
   | formula_npv OR formula_npv { if Config.symb_debug() then parse_warning "deprecated use of |"  ; pconjunction (purify $1) $3 }
   | formula_npv OROR formula_npv { mkOr ($1,$3) }
   | lvariable_npv COLON identifier { [P_PPred("type", [Arg_var $1;Arg_string($3)])] }
   | jargument_npv binop_cmp jargument_npv { Support_syntax.bop_to_prover_pred $2 $1 $3 }
   | jargument_npv EQUALS jargument_npv { Support_syntax.bop_to_prover_pred (Cmpeq) $1 $3 }
   | L_PAREN formula_npv R_PAREN { $2 }



spatial_at: 
   | jargument DOT field_signature MAPSTO  jargument { P_SPred("field", [$1; Arg_string(field_signature2str $3); $5] ) }
   | identifier L_PAREN jargument_list R_PAREN 
       {if List.length $3 =1 then P_SPred($1,$3 @ [mkArgRecord []]) else P_SPred($1,$3) }
   | full_identifier L_PAREN jargument_list R_PAREN {if List.length $3 =1 then P_SPred($1,$3 @ [mkArgRecord []]) else P_SPred($1,$3) }

spatial_list_ne: 
   | spatial_at MULT spatial_list_ne  { $1 :: $3 }
   | spatial_at    { [ $1 ] }

spatial_list: 
   | spatial_list_ne { $1 }
   |    { [] }

sequent:
   | spatial_list OR formula VDASH formula { ($1,$3,$5,mkEmpty) }
   | spatial_list OR formula VDASH formula DASHV formula { ($1,$3,$5,$7) }
/* used because the collapse form is || which is a reserved token */
   | spatial_list OROR formula VDASH formula {  if Config.symb_debug() then parse_warning "deprecated use of |" ; ($1,$3,$5,mkEmpty) }

sequent_list:
   |  /* empty */ { [] }
   | TRUE { [] }
   | sequent {[$1]}
   | sequent SEMICOLON sequent_list { $1::$3 }

sequent_list_or_list:
   |  sequent_list {[$1]}
   |  sequent_list ORTEXT sequent_list_or_list { $1::$3 }

identifier_op:
   | /* empty */ {""}
   | identifier  {$1}

without:
/*   | WITHOUT plain_list { $2 }*/
   | WITHOUT formula { ($2, mkEmpty) }
   | WITHOUT formula VDASH formula { ($2,$4) }
   | /* empty */ { (mkEmpty,mkEmpty) }

without_simp:
   | WITHOUT formula { $2 }
   | /* empty */ { [] }

varterm:
   | lvariable_list { Var(vs_from_list $1) }

clause: 
   | varterm NOTINCONTEXT { NotInContext($1) }
   | varterm NOTIN jargument { NotInTerm($1,$3) }

clause_list:
   | clause  { [$1] }
   | clause SEMICOLON clause_list {$1 :: $3}

where:
   | WHERE clause_list { $2 }
   | /* empty */ { [] }

ifclause:
/*   | IF plain_list { $2 }*/
   | /* empty plain term */ { [] } 
   | IF formula {$2}

/* Need to do tests that simplified rules are fine for pure bits.*/
equiv_rule:
   | EQUIV identifier_op COLON formula WAND formula BIMP formula without_simp  { EquivRule($2,$4,$6,$8,$9) } 
   | EQUIV identifier_op COLON formula IMP formula BIMP formula without_simp  { EquivRule($2,$4,$6,$8,$9) } 
   | EQUIV identifier_op COLON formula IMP formula without_simp  { EquivRule($2,$4,$6,mkEmpty,$7) } 
   | EQUIV identifier_op COLON formula BIMP formula without_simp  { EquivRule($2,mkEmpty,$4,$6,$7) } 

rule:
   | IMPORT STRING_CONSTANT SEMICOLON { ImportEntry($2) }
   |  RULE identifier_op COLON sequent without where IF sequent_list_or_list { NormalEntry(SeqRule($4,$8,$2,$5,$6)) }
   |  REWRITERULE identifier_op COLON identifier L_PAREN jargument_list R_PAREN EQUALS jargument ifclause without_simp where 
	 { NormalEntry(RewriteRule({function_name=$4;
				     arguments=$6;
				     result=$9;
				     guard={without_form=$11;rewrite_where=$12;if_form=$10};
				     rewrite_name=$2;
				     saturate=false})) }
   |  REWRITERULE identifier_op MULT COLON identifier L_PAREN jargument_list R_PAREN EQUALS jargument ifclause without_simp where 
	 { NormalEntry(RewriteRule({function_name=$5;
				     arguments=$7;
				     result=$10;
				     guard={without_form=$12;
					     rewrite_where=$13;
					     if_form=$11};
				     rewrite_name=$2;
				     saturate=true})) }
   |  ABSRULE identifier_op COLON formula LEADSTO formula where  { let seq=(mkEmpty,$4,mkEmpty,mkEmpty) in
							       let wo=(mkEmpty,mkEmpty) in 
							       let seq2=(mkEmpty,$6,mkEmpty,mkEmpty) in
							       let seq_list=[[seq2]] in
							       NormalEntry(SeqRule(seq,seq_list,$2,wo,$7)) }
   | equiv_rule { NormalEntry($1) }

rule_file:
   | EOF  { [] }
   | rule rule_file  {$1 :: $2}




boolean: 
   | TRUE { true }
   | FALSE { false }
;



question:
   | IMPLICATION COLON formula_npv VDASH formula_npv {Implication($3,$5)}
   | INCONSISTENCY COLON formula_npv {Inconsistency($3)}
   | FRAME COLON formula_npv VDASH formula_npv {Frame($3,$5)}
   | ABS COLON formula_npv {Abs($3)} 
   | ABDUCTION COLON formula_npv VDASH formula_npv {Abduction($3,$5)}


test:
   | IMPLICATION COLON formula_npv VDASH formula_npv QUESTIONMARK boolean {TImplication($3,$5,$7)}
   | INCONSISTENCY COLON formula_npv QUESTIONMARK boolean {TInconsistency($3,$5)}
   | FRAME COLON formula_npv VDASH formula_npv QUESTIONMARK formula_npv {TFrame($3,$5,$7)}
   | ABS COLON formula_npv QUESTIONMARK formula_npv {TAbs($3,$5)} 



question_file: 
   | EOF  { [] }
   | question question_file  {$1 :: $2}


test_file: 
   | EOF  { [] }
   | test test_file  {$1 :: $2}




ind_impl:
   | formula VDASH identifier L_PAREN jargument_list R_PAREN /* consider formula_npv*/
       {
	 if List.length $5 = 1
	 then ($1, $3,$5 @ [mkArgRecord []])
	 else ($1, $3,$5)
       }

ind_con:
   | identifier COLON ind_impl { {con_name = $1; con_def =$3} }

ind_con_list:
   |  /* empty */ { [] }
   | ind_con {[$1]}
   | ind_con SEMICOLON ind_con_list { $1::$3 }

inductive:
   | IMPORT STRING_CONSTANT SEMICOLON { IndImport($2) }
   | INDUCTIVE identifier L_PAREN jargument_list R_PAREN COLON ind_con_list 
       { 
	 let con_args = if List.length $4 = 1
	 then $4 @ [mkArgRecord []] else $4 in
	 IndDef{ind_name = $2; ind_args = con_args; ind_cons = $7} 
       }

inductive_file: 
   | EOF  { [] }
   | inductive inductive_file  {$1 :: $2}


%% (* trailer *)
