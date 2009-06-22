export OCAMLMAKEFILE = OcamlMakefile
export OCAMLYACC = ocamlyacc -v
export OCAMLC = ocamlc.opt -dtypes
export OCAMLOPT = ocamlopt.opt -dtypes
export OCAMLDEP = ocamldep.opt
export OCAMLDOC = ocamldoc.opt

ifndef BIN
	BIN := ../../bin
endif
export BIN

ifndef LIB
	LIB := ../../lib
endif
export LIB


INCLUDES = 

SYMBEXE_SOURCES = config.ml jparsetree.ml pprinter.mli pprinter.ml jlogic.ml specification.ml jparser.mly jlexer.mll methdec.ml cfg.ml abs.ml        support_symex.ml symexec.ml classverification.ml mkspecs.ml run_parser.ml

#dotty.ml

TOPLEVEL_SOURCES = $(SYMBEXE_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       LIBS="str utils sepprover" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       OCAMLFLAGS="-g -I ../prover -I ../utils" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/jstar.byte

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(BIN)/jstar

default: jstar

all: jstar

.PHONY: jstar.byte
jstar.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: jstar
jstar:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
