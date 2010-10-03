ifndef OCAMLMAKEFILE
	export OCAMLMAKEFILE = OcamlMakefile
endif
ifndef OCAMLYACC
	export OCAMLYACC = ocamlyacc -v
endif
ifndef OCAMLC
	export OCAMLC = ocamlc.opt -annot
endif 
ifndef OCAMLOPT
	export OCAMLOPT = ocamlopt.opt -annot -warn-error A
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

SYMBFRONT_SOURCES = symbfront.ml

TESTSYMB_SOURCES = test_symb.ml

DEFAULT_ARGS = LIBS="str unix utils prover_syntax symbexe_syntax jimple_syntax prover symbexe parsing" \
       OCAMLLDFLAGS="-I $(LIB)" \
       INCDIRS="../prover ../prover_syntax ../parsing ../symbexe_syntax ../utils ../jimple_syntax ../symbexe" \
       OCAMLFLAGS="" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) SOURCES="$(SYMBFRONT_SOURCES)" \
       RESULT=$(BIN)/run_symb.byte

MAINOPT = $(DEFAULT_ARGS) SOURCES="$(SYMBFRONT_SOURCES)" \
          RESULT=$(BIN)/run_symb

TMAIN = $(DEFAULT_ARGS) SOURCES="$(TESTSYMB_SOURCES)" \
       RESULT=$(BIN)/test_symb.byte 

TMAINOPT = $(DEFAULT_ARGS) SOURCES="$(TESTSYMB_SOURCES)" \
       RESULT=$(BIN)/test_symb 


default: run_symb test_symb

all: run_symb run_symb.byte

.PHONY: debug
debug: run_symb.byte test_symb.byte

prebuild: 
	@(cd ../prover; make)
	@(cd ../symbexe; make)

.PHONY: run_symb.byte  
run_symb.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 

.PHONY: run_symb
run_symb: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code
	
.PHONY: test_symb.byte  
test_symb.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(TMAIN) 

.PHONY: test_symb
test_symb: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(TMAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(TMAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(TMAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli .depend

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
