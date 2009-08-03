export OCAMLMAKEFILE = OcamlMakefile
export OCAMLYACC = ocamlyacc -v
export OCAMLC = ocamlc.opt -dtypes
export OCAMLOPT = ocamlopt.opt -dtypes
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


CORESOURCE =  rterm.ml rlogic.ml prover.ml sepprover.ml
#external_interface.mli 
#external_interface.ml  

PROVERSOURCE = $(CORESOURCE) load_logic.ml run.ml 

#TESTPROVERSOURCE = $(CORESOURCE) logic_parser.mly logic_lexer.mll load_logic.ml test.ml
TESTPROVERSOURCE = $(CORESOURCE)  load_logic.ml test.ml

#LIBRARYSOURCE = $(CORESOURCE) logic_parser.mly logic_lexer.mll load_logic.ml
LIBRARYSOURCE = $(CORESOURCE)  load_logic.ml

DEFAULT_ARGS = LIBS="str utils parser" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       OCAMLFLAGS="-g -I ../utils -I ../syntax" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) SOURCES="$(PROVERSOURCE)" \
       RESULT=$(BIN)/run_logic.byte 

MAINOPT = $(DEFAULT_ARGS) SOURCES="$(PROVERSOURCE)" \
       RESULT=$(BIN)/run_logic

TMAIN = $(DEFAULT_ARGS) SOURCES="$(TESTPROVERSOURCE)" \
       RESULT=$(BIN)/testharness.byte 

TMAINOPT = $(DEFAULT_ARGS) SOURCES="$(TESTPROVERSOURCE)" \
       RESULT=$(BIN)/testharness 

#       LIBS="str" \

LIBRARY = SOURCES="$(LIBRARYSOURCE)" \
       OCAMLLDFLAGS="-g -a" \
       OCAMLFLAGS="-g -I ../utils -I ../syntax" \
       RESULT="$(LIB)/sepprover.cmxa" \
       TRASH=""
BLIBRARY = SOURCES="$(LIBRARYSOURCE)" \
       OCAMLLDFLAGS="-g -a" \
       OCAMLFLAGS="-g -I ../utils -I ../syntax" \
       RESULT="$(LIB)/sepprover.cma" \
       TRASH=""

default: toplevel testharness sepprover.cmxa

all: toplevel testharness

.PHONY: toplevel.byte
toplevel.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) byte-code


.PHONY: toplevel
toplevel:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

sepprover.cmxa: 
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) native-code

sepprover.cma: 
	$(MAKE) -f $(OCAMLMAKEFILE) $(BLIBRARY) byte-code

.PHONY: testharness.byte
testharness.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(TMAIN) byte-code


.PHONY: testharness
testharness:
	$(MAKE) -f $(OCAMLMAKEFILE) $(TMAINOPT) native-code



clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN2) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT2) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc logic_parser.output *~ *.dll *.exe *.cmi *.cmx *.o logic_parser.ml logic_lexer.ml logic_parser.mli logic_lexer.mli

prover.dll: $(CORESOURCE)
	$(FSHARPCOMPILER) -a $(CORESOURCE) -o prover.dll

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
