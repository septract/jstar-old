open Ast
open Format
open Std

let _ =
  let lexbuf = Lexing.from_channel stdin in
  let input = Parser.mli Lexer.token lexbuf in
  let output = List.fold_left Generate.merge_modules Generate.empty_module
    & List.map ((|>) input) [Generate.evaluator; Generate.mapper] in
  Code.check_module output;
  Code.pp_module std_formatter output
