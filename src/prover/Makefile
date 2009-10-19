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


CORESOURCE = rterm.ml rlogic.ml prover.ml sepprover.ml
LIBRARYSOURCE = $(CORESOURCE)

LIBRARY = SOURCES="$(LIBRARYSOURCE)" \
       OCAMLLDFLAGS="-g -a" \
       INCDIRS="../utils" \
       OCAMLFLAGS="-g" \
       RESULT="$(LIB)/sepprover.cmxa" \
       TRASH=""
BLIBRARY = SOURCES="$(LIBRARYSOURCE)" \
       OCAMLLDFLAGS="-g -a" \
       INCDIRS="../utils" \
       OCAMLFLAGS="-g" \
       RESULT="$(LIB)/sepprover.cma" \
       TRASH=""

default: sepprover.cmxa

prebuild: 
	@(cd ../utils; make)

all: default


sepprover.cmxa: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) native-code

ssepprover.cma: prebuild
	@$(MAKE) -f $(OCAMLMAKEFILE) $(BLIBRARY) byte-code

clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(LIBRARY) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(BLIBRARY) clean
	rm -f *.annot doc/*.html doc/*.css doc/test.odoc logic_parser.output *~ *.dll *.exe *.cmi *.cmx *.o logic_parser.ml logic_lexer.ml logic_parser.mli logic_lexer.mli

prover.dll: $(CORESOURCE)
	$(FSHARPCOMPILER) -a $(CORESOURCE) -o prover.dll

.depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

dummy:

include .depend
