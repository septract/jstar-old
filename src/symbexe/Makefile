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

SYMBEXE_SOURCES = symbexespec.ml methdec_core.ml pprinter_core.ml cfg_core.ml symexec.ml

TOPLEVEL_SOURCES = $(SYMBEXE_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       OCAMLLDFLAGS="-g -a " \
       INCDIRS="../prover ../prover_syntax ../symbexe_syntax ../utils" \
       OCAMLFLAGS="-g" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(LIB)/symbexe.cma

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(LIB)/symbexe.cmxa

default: symbexe.cmxa

.PHONY: debug
debug: symbexe.cma

all: default debug

prebuild: 
	@(cd ../prover; make)

symbexe.cma: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


symbexe.cmxa: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
