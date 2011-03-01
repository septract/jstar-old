ifndef JSTAR_HOME
	JSTAR_HOME=$(CURDIR)
endif
export JSTAR_HOME

build:
	$(MAKE) -C src

test: build
	$(MAKE) -s -C unit_tests

doc:
	$(MAKE) -C doc/tutorial

scripts:
	$(MAKE) -C scripts

all: build test

clean:
	rm -f lib/*.a lib/*.cmxa lib/*.cmxs bin/*.cmxs
	$(MAKE) -C src clean
	$(MAKE) -C unit_tests clean
	$(MAKE) -C scripts clean
	$(MAKE) -C doc/tutorial clean

.PHONY: build test doc scripts all clean

# Experimental ocamlbuild stuff
DIRS=parsing prover prover_syntax symbexe symbexe_syntax utils jimple_syntax\
		 jimplefront proverfront symbfront abs_int plugin_interface
MAINS=run_parser run symbfront jStar

LIBS=str unix zip dynlink
CFLAGS=-annot,-I,+zip#,-warn-error,A
LFLAGS=-I,+zip
OB=ocamlbuild -cflags $(CFLAGS) -lflags $(LFLAGS) $(LIBS:%=-lib %)

ob: clean
	@$(OB) $(DIRS:%=-I src/%) $(MAINS:=.native)

ob-test: ob
	cd unit_tests/cli && ./io_test.sh -q

ob-clean:
	@ocamlbuild -clean -quiet
	$(MAKE) -C unit_tests/cli clean

-include .install.mk

#vim:noet:
