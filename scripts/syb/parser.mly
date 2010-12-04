/* Parser for mli files that contain only simple type declarations. */

%{
open Ast
open Format

let print_pos ppf {
  Lexing.pos_fname=_;
  Lexing.pos_lnum=l;
  Lexing.pos_cnum=c;
  Lexing.pos_bol=b
} = fprintf ppf "%d:%d" l (c - b + 1)
%}

%token AND
%token ARROW
%token BAR
%token COLON
%token EOF
%token EQUAL
%token DOT
%token <string> LIDENT
%token LP
%token OF
%token RP
%token STAR
%token TYPE
%token <string> UIDENT
%token VAL

%right ARROW

%start mli
%type <Ast.ml_type list> mli

%%

mli:
    EOF {[]}
  | phrase mli {$1@$2}
;
phrase:
    TYPE type_declarations {List.rev $2}
  | VAL val_ident COLON core_type {[]}
  | error {
      eprintf "skipped %a--%a\n" 
        print_pos (Parsing.symbol_start_pos())
        print_pos (Parsing.symbol_end_pos());
      []}
;
type_declarations:
    type_declaration {[$1]}
  | type_declarations AND type_declaration {$3::$1}
;
type_declaration:
    LIDENT type_kind {{type_name=$1;type_kind=$2}}
;
type_kind:
    {TK_abstract}
  | EQUAL simple_core_type_or_tuple {TK_synonym $2}
  | EQUAL constructor_declarations {TK_variant(List.rev $2)}
;
constructor_declarations:
    constructor_declaration {[$1]}
  | constructor_declarations BAR constructor_declaration {$3::$1}
;
constructor_declaration:
    UIDENT constructor_arguments {($1,$2)}
;
constructor_arguments:
    {TE_tuple []}
  | OF core_type_list {TE_tuple(List.rev $2)}
;
core_type_list:
    simple_core_type {[$1]}
  | core_type_list STAR simple_core_type {$3::$1}
;
core_type:
    simple_core_type_or_tuple {$1}
  | core_type ARROW core_type {TE_arrow($1,$3)}
;
simple_core_type_or_tuple:
    simple_core_type {$1}
  | simple_core_type STAR core_type_list {TE_tuple($1::List.rev $3)}
;
simple_core_type:
    type_longident {TE_id $1}
  | simple_core_type LIDENT {TE_application($2,$1)}
  | LP core_type RP {$2}
;
type_longident:
    LIDENT {Id $1}
  | mod_longident DOT LIDENT {Dot($1,$3)}
;
mod_longident:
    UIDENT {Id $1}
  | mod_longident DOT UIDENT {Dot($1,$3)}
;
val_ident:
    LIDENT {()}
;
/* vim:filetype=text: 
*/
