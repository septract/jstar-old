(********************************************************
   This file is part of jStar 
	src/utils/dot.mli
   Release 
        $Release$
   Version 
        $Rev$
   $Copyright$
   
   jStar is distributed under a BSD license,  see, 
      LICENSE.txt
 ********************************************************)

let escape_for_label s = 
  Str.global_replace (Str.regexp "\\\\n") "\\l" (String.escaped s)

