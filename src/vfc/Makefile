ifndef OCAMLMAKEFILE
	export OCAMLMAKEFILE = OcamlMakefile
endif
ifndef OCAMLYACC
	export OCAMLYACC = ocamlyacc -v
endif
ifndef OCAMLC
	export OCAMLC = ocamlc.opt -annot -g
endif 
ifndef OCAMLOPT
	export OCAMLOPT = ocamlopt.opt -annot -g
endif 
ifndef OCAMLDEP
	export OCAMLDEP = ocamldep.opt
endif 
ifndef OCAMLDOC
	export OCAMLDOC = ocamldoc.opt
endif 

ifndef BIN
	BIN := ../../bin
endif
export BIN

ifndef LIB
	LIB := ../../lib
endif
export LIB


INCLUDES = 

VFCFRONT_SOURCES = vfcAST.ml vfcparse.mly vfclex.mll vfclogic.ml vfc2core.ml vfcfront.ml

DEFAULT_ARGS = SOURCES="$(VFCFRONT_SOURCES)" \
       LIBS="str unix utils prover_syntax symbexe_syntax jimple_syntax prover symbexe parsing" \
       OCAMLLDFLAGS="-I $(LIB)" \
       INCDIRS="../prover ../prover_syntax ../parsing ../symbexe_syntax ../utils ../jimple_syntax ../symbexe" \
       OCAMLFLAGS="" \
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
