/********************************************************
   This file is part of jStar 
	src/prover/smtparse.ml
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************/

%{ (* header *)

open Smtsyntax 

%} 

%token LPAREN
%token RPAREN
%token UNSUPPORTED
%token SUCCESS
%token ERROR
%token SAT
%token UNSAT
%token UNKNOWN
%token <string> STRING_CONSTANT

%start main             /* the entry point */
%type <Smtsyntax.smt_response> main
%%
main: 
  | UNSUPPORTED                           { Unsupported }
  | SUCCESS                               { Success }
  | LPAREN ERROR STRING_CONSTANT RPAREN   { Error $3 }
  | SAT                                   { Sat }
  | UNSAT                                 { Unsat }
  | UNKNOWN                               { Unknown }
;
