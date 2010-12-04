open Ast
open Format

let _ =
  let lexbuf = Lexing.from_channel stdin in
  let input = Parser.mli Lexer.token lexbuf in
  let output = Generator.process input in
  Code.print std_formatter output
