export OCAMLMAKEFILE = OcamlMakefile
export OCAMLYACC = ocamlyacc -v
export OCAMLC = ocamlc.opt -annot
export OCAMLOPT = ocamlopt.opt -annot
export OCAMLDEP = ocamldep.opt
export OCAMLDOC = ocamldoc.opt

export FSHARPDIR = /Users/mjp41/FSharp-1.9.6.2
export MONO = mono
export FSHARPCOMPILER = $(MONO) $(FSHARPDIR)/bin/fsc.exe --mlcompatibility -r $(FSHARPDIR)/bin/FSharp.PowerPack.dll
export MAKEDLL = $(FSHARPCOMPILER) -a 


INCLUDES = 

ifndef BIN
	BIN := ../../bin
endif
export BIN

ifndef LIB
	LIB := ../../lib
endif
export LIB


#external_interface.mli 
#external_interface.ml  

PROVERSOURCE = run.ml 

#TESTPROVERSOURCE = $(CORESOURCE) logic_parser.mly logic_lexer.mll load_logic.ml test.ml
TESTPROVERSOURCE = inductive.ml test.ml


DEFAULT_ARGS = LIBS="str utils prover_syntax prover symbexe_syntax jimple_syntax parsing" \
       OCAMLLDFLAGS=" -I $(LIB)" \
       INCDIRS="../utils ../prover_syntax ../prover ../parsing"
       OCAMLFLAGS="" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) SOURCES="$(PROVERSOURCE)" \
       RESULT=$(BIN)/run_logic.byte 

MAINOPT = $(DEFAULT_ARGS) SOURCES="$(PROVERSOURCE)" \
       RESULT=$(BIN)/run_logic

TMAIN = $(DEFAULT_ARGS) SOURCES="$(TESTPROVERSOURCE)" \
       RESULT=$(BIN)/test_logic.byte 

TMAINOPT = $(DEFAULT_ARGS) SOURCES="$(TESTPROVERSOURCE)" \
       RESULT=$(BIN)/test_logic 

#       LIBS="str" \

default: toplevel test_logic

.PHONY: debug
debug: toplevel.byte test_logic.byte

prebuild: 
	@(cd ../prover; make)
	@(cd ../parsing; make)

all: toplevel test_logic

.PHONY: toplevel.byte
toplevel.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) byte-code


.PHONY: toplevel
toplevel: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

.PHONY: test_logic.byte
test_logic.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(TMAIN) byte-code


.PHONY: test_logic
test_logic: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(TMAINOPT) native-code



clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(TMAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(TMAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc logic_parser.output *~ *.dll *.exe *.cmi *.cmx *.o logic_parser.ml logic_lexer.ml logic_parser.mli logic_lexer.mli

prover.dll: $(CORESOURCE)
	$(FSHARPCOMPILER) -a $(CORESOURCE) -o prover.dll

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
