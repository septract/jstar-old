/******************************************************************
     Separation logic theorem prover

    Copyright Matthew Parkinson & Dino Distefano
 
*******************************************************************/

/* implementation of a parser for internal logic */

%{ (* header *)

open Vars
open Pterm
open Plogic
open Rlogic
open Prover
open Lexing
open Parsing 

let newPVar x = PVar(0,x)

let newAnyVar x = AnyVar(0,x)

let newEVar x = EVar(0,x)


let location_to_string pos = 
  Printf.sprintf "Line %d character %d" pos.pos_lnum  (pos.pos_cnum - pos.pos_bol + 1)

let parse_error s =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  Printf.printf "Error between %s and %s\n" (location_to_string start_pos) (location_to_string end_pos)



%} /* declarations */

/* ============================================================= */
/* tokens */

%token <string> IDENTIFIER
%token <string> STRING
%token UNDERSCORE
%token LEFTPAREN
%token RIGHTPAREN
%token L_BRACE
%token R_BRACE
%token COMMA
%token COLON
%token SEMICOLON
%token VDASH
%token LEADSTO
%token STAR
%token QUESTIONMARK
%token <string> STRING
%token BAR
%token EOF
%token EQUAL
%token NOTEQUAL
%token FALSE
%token TRUE
%token IMPLICATION
%token FRAME
%token ABS
%token ABSRULE
%token INCONSISTENCY
%token RULE
%token PURERULE
%token PRED
%token REWRITERULE
%token EMPRULE
%token IF
%token WITHOUT
%token WHERE
%token EV
%token NOTIN
%token NOTINCONTEXT
%token OR
%token GARBAGE
%token IMPORT 

/* ============================================================= */

%left IDENTIFIER
%left STAR




/* entry points */

%start file
%type <Prover.question list> file

%start rule_file
%type <Prover.rules list> rule_file

%start test_file
%type <Prover.test list> test_file


%% /* rules */

/* entry points */
identifier:
   | IDENTIFIER { $1 }
;
variable:
   | UNDERSCORE identifier { newEVar($2) }
   | identifier { newPVar($1) }
   | QUESTIONMARK identifier { newAnyVar($2) }
;
boolean: 
   | TRUE { true }
   | FALSE { false }
;
fldlist: 
   | identifier EQUAL argument { [($1,$3)] }
   | /*empty*/ { [] }
   | identifier EQUAL argument SEMICOLON fldlist  { ($1,$3) :: $5 }
;
argument:
   | variable {Arg_var ($1)}
   | identifier LEFTPAREN argument_list RIGHTPAREN { Arg_op($1,$3) }
   | STRING {Arg_string($1)}
   | L_BRACE fldlist R_BRACE {mkArgRecord $2}
;
argument_list:
   | /*empty*/  {[]}
   | argument {$1::[]}
   | argument COMMA argument_list {$1::$3}
;
plain: 
   | identifier LEFTPAREN argument_list RIGHTPAREN { mkPPred($1,$3) }
   | argument EQUAL argument { mkEQ($1,$3) }
   | argument NOTEQUAL argument { mkNEQ($1,$3) }
;
plain_list:
   | TRUE { [] }
   |      { [] }
   | plain { $1 }
   | plain STAR plain_list {$1 &&& $3}
;
spatial_comp:
   | identifier LEFTPAREN argument_list RIGHTPAREN { mkSPred($1,$3) }
   | FALSE { mkFalse}
   | GARBAGE { mkGarbage }
   | LEFTPAREN formula RIGHTPAREN BAR BAR LEFTPAREN formula RIGHTPAREN { mkOr($2,$7) }
;
spatial:
   | identifier LEFTPAREN argument_list RIGHTPAREN { mkSPred($1,$3) }
;
spatial_comp_list:
   |      { [] }
   | spatial_comp { $1 }
   | spatial_comp STAR spatial_comp_list {$1  &&& $3} 
;
spatial_list:
   |      { [] }
   | spatial { $1 }
   | spatial STAR spatial_list {$1 &&& $3} 
;
formula:
   | plain_list BAR spatial_comp_list { $3 &&& $1 }
;


question:
   | IMPLICATION COLON formula VDASH formula {Implication($3,$5)}
   | INCONSISTENCY COLON formula {Inconsistency($3)}
   | FRAME COLON formula VDASH formula {Frame($3,$5)}
   | EQUAL COLON formula VDASH argument EQUAL argument {Equal($3,$5,$7)} 
   | ABS COLON formula {Abs($3)} 

test:
   | IMPLICATION COLON formula VDASH formula QUESTIONMARK boolean {TImplication($3,$5,$7)}
   | INCONSISTENCY COLON formula QUESTIONMARK boolean {TInconsistency($3,$5)}
   | FRAME COLON formula VDASH formula QUESTIONMARK formula {TFrame($3,$5,$7)}
   | EQUAL COLON formula VDASH argument EQUAL argument QUESTIONMARK boolean {TEqual($3,$5,$7,$9)} 
   | ABS COLON formula QUESTIONMARK formula {TAbs($3,$5)} 

sequent:
   | spatial_list BAR formula VDASH formula { ($1,$3,$5) }

sequent_list:
   |  /* empty */ { [] }
   | TRUE { [] }
   | sequent {[$1]}
   | sequent SEMICOLON sequent_list { $1::$3 }

sequent_list_or_list:
   |  sequent_list {[$1]}
   |  sequent_list OR sequent_list_or_list { $1::$3 }

/*
plain_list_or_list:
   |  plain_list {[$1]}
   |  plain_list OR plain_list_or_list { $1::$3 }
*/

identifier_op:
   | /* empty */ {""}
   | identifier  {$1}

without:
   | WITHOUT plain_list { $2 }
   | WITHOUT formula { $2 }
   | /* empty */ { [] }

variable_list:
   | /* empty */ { vs_empty }
   | variable { vs_add $1 vs_empty }
   | variable COMMA variable_list { vs_add $1 $3 }

varterm:
   | variable_list { Var($1) }
   | EV argument { EV($2) }

clause: 
   | varterm NOTINCONTEXT { NotInContext($1) }
   | varterm NOTIN argument { NotInTerm($1,$3) }

clause_list:
   | clause  { [$1] }
   | clause SEMICOLON clause_list {$1 :: $3}

where:
   | WHERE clause_list { $2 }
   | /* empty */ { [] }

/*bitlist:
   |      { false::[] }
   | STAR               { true::[] }
   | STAR COMMA bitlist { true::$3 }
   | COMMA bitlist { false::$2 }
*/

ifclause:
   | IF plain_list { $2 }
   | /* empty plain term */ { [] } 
   | IF formula {$2}

rule:
   | IMPORT STRING SEMICOLON { Import($2) }
   |  RULE identifier_op COLON sequent without where IF sequent_list_or_list { SeqRule($4,$8,$2,$5,$6) }
   |  REWRITERULE identifier_op COLON identifier LEFTPAREN argument_list RIGHTPAREN EQUAL argument ifclause without where { RewriteRule($4,$6,$9,$11,$12,$10,$2,false) }
   |  REWRITERULE identifier_op STAR COLON identifier LEFTPAREN argument_list RIGHTPAREN EQUAL argument ifclause without where { RewriteRule($5,$7,$10,$12,$13,$11,$2,true) }
   |  ABSRULE identifier_op COLON formula LEADSTO formula where  { let seq=([],$4,[]) in
							       let wo=[] in 
							       let seq2=([],$6,[]) in
							       let seq_list=[[seq2]] in
							       SeqRule(seq,seq_list,$2,wo,$7) }

rule_file:
   | EOF  { [] }
   | rule rule_file  {$1 :: $2}

file: 
   | EOF  { [] }
   | question file  {$1 :: $2}

test_file: 
   | EOF  { [] }
   | test test_file  {$1 :: $2}


