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

SOURCES = config.ml support_syntax.ml logic_parser.mly logic_lexer.mll jparser.mly jlexer.mll

LIBRARY = SOURCES="$(SOURCES)" \
       OCAMLLDFLAGS="-g -a" \
       OCAMLFLAGS="-g  -I ../utils" \
       RESULT="$(LIB)/parser.cmxa" \
       TRASH=""

BLIBRARY = SOURCES="$(SOURCES)" \
       OCAMLLDFLAGS="-g -a" \
       OCAMLFLAGS="-g -I ../utils" \
       RESULT="$(LIB)/parser.cma" \
       TRASH=""

parser.cmxa: 
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) native-code

parser.cma: 
	$(MAKE) -f $(OCAMLMAKEFILE) $(BLIBRARY) byte-code


clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
