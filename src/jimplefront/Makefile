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

SYMBEXE_SOURCES = support_symex.ml jlogic.ml javaspecs.ml methdec.ml translatejimple.ml classverification.ml mkspecs.ml run_parser.ml


TOPLEVEL_SOURCES = $(SYMBEXE_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       LIBS="str unix utils prover_syntax symbexe_syntax jimple_syntax sepprover symbexe parser" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       INCDIRS="../prover ../prover_syntax ../parsing ../symbexe_syntax ../utils ../jimple_syntax ../symbexe" \
       OCAMLFLAGS="-g" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/jstar.byte

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(BIN)/jstar

default: jstar

.PHONY: debug
debug: jstar.byte

all: jstar jstar.byte


prebuild: 
	@(cd ../prover; make)
	@(cd ../jimple_syntax; make)
	@(cd ../symbexe; make)

.PHONY: jstar.byte  
jstar.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: jstar
jstar: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
