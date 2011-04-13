ifndef LIB
	LIB := ../../lib
endif
export LIB

SOURCES = support_syntax.ml jparser.mly jlexer.mll load_logic.ml

CORESTAR_INCLUDES = utils prover_syntax symbexe_syntax
JSTAR_INCLUDES = jimple_syntax
RESULT = "$(LIB)/parsing"
OCAMLLDFLAGS="-a"

include ../Makefile.jstar