build:
	$(MAKE) -C src

test: build
	$(MAKE) -s -C unit_tests

doc:
	$(MAKE) -C doc/tutorial

scripts:
	$(MAKE) -C scripts

all: build test scripts doc

clean:
	rm -f lib/*.a
	$(MAKE) -C src clean
	$(MAKE) -C unit_tests clean
	$(MAKE) -C scripts clean
	$(MAKE) -C doc/tutorial clean

.PHONY: build test doc scripts all clean

# Experimental ocamlbuild stuff
DIRS=parsing prover prover_syntax symbexe symbexe_syntax utils jimple_syntax\
		 jimplefront proverfront symbfront
MAINS=run_parser run symbfront jStar

LIBS=str unix zip
CFLAGS=-annot,-I,+zip#,-warn-error,A
LFLAGS=-I,+zip
OB=ocamlbuild -cflags $(CFLAGS) -lflags $(LFLAGS) $(LIBS:%=-lib %)

ob: clean
	@$(OB) $(DIRS:%=-I src/%) $(MAINS:=.native)

ob-clean:
	@ocamlbuild -clean -quiet
	@rm -rf htmldoc

#vim:noet:
