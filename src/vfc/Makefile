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

ABDUCTFRONT_SOURCES = vfcAST.ml vfcparse.mly vfclex.mll vfc2core.ml vfcfront.ml


TOPLEVEL_SOURCES = $(ABDUCTFRONT_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       LIBS="str unix utils prover_syntax symbexe_syntax prover" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       INCDIRS="../utils ../prover_syntax ../symbexe_syntax ../prover" \
       OCAMLFLAGS="-g" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/run_vfc.byte

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(BIN)/run_vfc

default: run_vfc

.PHONY: debug
debug: run_vfc.byte

all: run_vfc run_vfc.byte


prebuild: 
	@(cd ../prover; make)
	@(cd ../symbexe; make)

.PHONY: run_vfc.byte  
run_vfc.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: run_vfc
run_vfc: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli .depend

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
