ifndef LIB
	LIB := ../../lib
endif
export LIB

SOURCES = congruence.ml cterm.mli cterm.ml clogic.mli clogic.ml \
         smtsyntax.ml smtparse.mly smtlex.mll smt.ml prover.ml sepprover.ml
INCLUDES = utils prover_syntax plugin_interface
RESULT = "$(LIB)/prover"
OCAMLLDFLAGS="-a"

include ../Makefile.jstar
