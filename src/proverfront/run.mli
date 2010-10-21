(********************************************************
   This file is part of jStar
        src/proverfront/run.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val program_file_name : string ref
val logic_file_name : string ref
val arg_list : (string * Arg.spec * string) list
val main : unit -> unit
