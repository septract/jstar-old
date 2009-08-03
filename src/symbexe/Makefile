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

SYMBEXE_SOURCES = jlogic.ml specification.ml support_symex.ml methdec.ml cfg.ml abs.ml symexec.ml classverification.ml mkspecs.ml run_parser.ml


TOPLEVEL_SOURCES = $(SYMBEXE_SOURCES)

DEFAULT_ARGS = SOURCES="$(TOPLEVEL_SOURCES)" \
       LIBS="str unix utils parser sepprover" \
       OCAMLLDFLAGS="-g -I $(LIB)" \
       OCAMLFLAGS="-g -I ../prover -I ../utils -I ../syntax" \
       TRASH=""

MAIN = $(DEFAULT_ARGS) RESULT=$(BIN)/jstar.byte

MAINOPT = $(DEFAULT_ARGS)  RESULT=$(BIN)/jstar

default: jstar

all: jstar

#Needs to rebuild as OcamlMakefile does relink if a library changes.
.prover: ../../lib/sepprover.cmxa
	touch .prover
	make clean
	cd ../prover; make

.PHONY: jstar.byte  
jstar.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) 


.PHONY: jstar
jstar: .prover
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
