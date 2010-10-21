(********************************************************
   This file is part of jStar
        src/jimplefront/arg_file_lexer.mll
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


rule arg = parse
  | [^ ' ' '\t' '\n' '\r' '"']+ as a { Some a }
  | '"' ([^ '"' '\n' '\r']* as a) '"' { Some a }
  | eof { None }
  | _ { arg lexbuf }
