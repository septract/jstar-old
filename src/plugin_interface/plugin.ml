(********************************************************
   This file is part of jStar
        src/plugins/plugin.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


type abs_int =
{
  abstract_val : (Psyntax.pform -> Psyntax.pform) ref option;
  join : (Psyntax.pform -> Psyntax.pform -> Psyntax.pform) ref option;
  meet : (Psyntax.pform -> Psyntax.pform -> Psyntax.pform) ref option;
  widening : (Psyntax.pform -> Psyntax.pform -> Psyntax.pform) ref option;
}
