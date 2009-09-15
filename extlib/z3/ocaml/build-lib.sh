#!/bin/bash
if [-n $1]; then 
    export OCAMLLIB=$1
else
    export OCAMLLIB=/usr/local/lib/ocaml
fi
gcc -I../include -I$OCAMLLIB -c z3_stubs.c
ocamlopt -c z3.mli
ocamlopt -c z3.ml
ar rcs libz3stubs.a z3_stubs.o
ar rcs libz3stubs.a libz3.so
ranlib libz3stubs.a
ocamlopt -a -o z3.cmxa -cclib -lz3stubs z3.cmx
