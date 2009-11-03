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

SOURCES = misc.ml system.ml vars.ml debug.ml jparsetree.ml jimple_global_types.ml pprinter.ml
#dotty.ml

LIBRARY = SOURCES="$(SOURCES)" \
       OCAMLLDFLAGS="-g -a" \
       OCAMLFLAGS="-g" \
       RESULT="$(LIB)/utils.cmxa" \
       TRASH=""

BLIBRARY = SOURCES="$(SOURCES)" \
       OCAMLLDFLAGS="-g -a" \
       OCAMLFLAGS="-g" \
       RESULT="$(LIB)/utils.cma" \
       TRASH=""

utils.cmxa: 
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) native-code

utils.cma: 
	$(MAKE) -f $(OCAMLMAKEFILE) $(BLIBRARY) byte-code


clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output *.cmi *.cmx *.o

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
