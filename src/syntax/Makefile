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

SOURCES = config.ml support_syntax.ml jparser.mly jlexer.mll load_logic.ml

LIBRARY = SOURCES="$(SOURCES)" \
       OCAMLLDFLAGS="-g -a" \
       INCDIRS="../utils ../prover" \
       OCAMLFLAGS="-g" \
       RESULT="$(LIB)/parser.cmxa" \
       TRASH=""

BLIBRARY = SOURCES="$(SOURCES)" \
       OCAMLLDFLAGS="-g -a" \
       INCDIRS="../utils ../prover" \
       OCAMLFLAGS="-g" \
       RESULT="$(LIB)/parser.cma" \
       TRASH=""

parser.cmxa: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) native-code

parser.cma: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(BLIBRARY) byte-code

prebuild:
	@(cd ../prover; make)

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc jparser.output  *.cmi *.cmx *.o jparser.ml jlexer.ml jparser.mli jlexer.mli logic_parser.ml logic_lexer.ml logic_parser.mli logic_lexer.mli

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
