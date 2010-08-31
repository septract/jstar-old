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
       LIBS="str unix utils prover_syntax symbexe_syntax jimple_syntax prover symbexe parsing" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       INCDIRS="../prover ../prover_syntax ../parsing ../symbexe_syntax ../utils ../jimple_syntax ../symbexe" \
       OCAMLFLAGS="-g" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/run_symb.byte

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(BIN)/run_symb

default: run_symb

.PHONY: debug
debug: run_symb.byte

all: run_symb run_symb.byte


prebuild: 
	@(cd ../prover; make)
	@(cd ../symbexe; make)

.PHONY: run_symb.byte  
run_symb.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: run_symb
run_symb: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli .depend

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
