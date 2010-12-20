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

SYNTACTIC_SOURCES = syntactic.ml

DEFAULT_ARGS = LIBS="str unix utils prover_syntax prover plugin_interface" \
       OCAMLLDFLAGS="-I $(LIB)" \
       INCDIRS="../utils ../prover_syntax ../prover ../plugin_interface" \
       OCAMLFLAGS="" \
       TRASH=""

BYTECODE_LIBRARY = $(DEFAULT_ARGS) SOURCES="$(SYNTACTIC_SOURCES)" \
       RESULT=$(BIN)/syntactic

SHARED_LIBRARY = $(DEFAULT_ARGS) SOURCES="$(SYNTACTIC_SOURCES)" \
          RESULT=$(BIN)/syntactic

default: syntactic_shared

all: syntactic syntactic_shared

.PHONY: debug
debug: syntactic

prebuild: 
	@(cd ../prover; make)
	@(cd ../plugin_interface; make)

.PHONY: syntactic
syntactic: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(BYTECODE_LIBRARY) byte-code-library

.PHONY: syntactic_shared
syntactic_shared: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(SHARED_LIBRARY) shared-code-library
	
clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(BYTECODE_LIBRARY) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(SHARED_LIBRARY) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli .depend

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
