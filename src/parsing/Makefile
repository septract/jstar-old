ifndef LIB
	LIB := ../../lib
endif
export LIB

SOURCES =   support_syntax.ml jparser.mly jlexer.mll load_logic.ml

INCLUDES = utils prover_syntax symbexe_syntax jimple_syntax
RESULT = "$(LIB)/parsing"
OCAMLLDFLAGS="-a"

include ../Makefile.jstar