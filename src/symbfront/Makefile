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

SYMBFRONT_SOURCES = symbfront.ml


TOPLEVEL_SOURCES = $(SYMBFRONT_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       LIBS="str unix utils prover_syntax symbexe_syntax jimple_syntax sepprover symbexe parser" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       INCDIRS="../prover ../prover_syntax ../parsing ../symbexe_syntax ../utils ../jimple_syntax ../symbexe" \
       OCAMLFLAGS="-g" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/jeffree.byte

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(BIN)/jeffree

default: jeffree

.PHONY: debug
debug: jeffree.byte

all: jeffree jeffree.byte


prebuild: 
	@(cd ../prover; make)
	@(cd ../symbexe; make)

.PHONY: jeffree.byte  
jeffree.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: jeffree
jeffree: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli .depend

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
