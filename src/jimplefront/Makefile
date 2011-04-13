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

JIMPLEFRONT_SOURCES = support_symex.ml jlogic.ml javaspecs.ml methdec.ml translatejimple.ml classverification.ml mkspecs.ml run_parser.ml


TOPLEVEL_SOURCES = $(JIMPLEFRONT_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       LIBS="str unix dynlink utils prover_syntax symbexe_syntax plugin_interface prover symbexe jimple_syntax parsing" \
       OCAMLLDFLAGS=" -I $(LIB) -I $(CORESTAR_HOME)/lib" \
       INCDIRS="$(CORESTAR_HOME)/src/prover $(CORESTAR_HOME)/src/prover_syntax $(CORESTAR_HOME)/src/symbexe_syntax $(CORESTAR_HOME)/src/utils $(CORESTAR_HOME)/src/symbexe $(CORESTAR_HOME)/src/plugin_interface ../parsing ../jimple_syntax" \
       OCAMLFLAGS="" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/jstar.byte

MAINOPT = $(DEFAULT_ARGS) RESULT=$(BIN)/jstar

default: jstar

.PHONY: debug
debug: jstar.byte

all: jstar jstar.byte


prebuild:
	@$(MAKE) -C ../jimple_syntax
	@$(MAKE) -C ../parsing

.PHONY: jstar.byte  
jstar.byte: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: jstar
jstar: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli .depend

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
# vim:noet:
