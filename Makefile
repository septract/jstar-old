# configurations

ifndef CORESTAR_HOME
	CORESTAR_HOME=$(CURDIR)/../corestar
endif
export CORESTAR_HOME

ifndef JSTAR_HOME
	JSTAR_HOME=$(CURDIR)
endif
export JSTAR_HOME

SRC_DIRS=src corestar_src
MAINS=jstar
LIBS=dynlink str unix

# section with stuff that shouldn't change often

SHELL=/bin/bash
SRC_SUBDIRS=$(addsuffix .subdirs,$(SRC_DIRS))
OCAMLBUILD=ocamlbuild `cat $(SRC_SUBDIRS)` $(addprefix -lib ,$(LIBS))

build: native

native byte: $(SRC_SUBDIRS)
	$(OCAMLBUILD) $(addsuffix .$@,$(MAINS))
	for f in $(MAINS); do ln -sf ../`readlink $$f.$@` bin/$$f; rm $$f.$@; done

test: test-native

test-native test-byte: test-%: %
	$(MAKE) -s -C unit_tests

doc:
	$(MAKE) -C doc/tutorial

scripts:
	$(MAKE) -C scripts

all: build test

clean:
	ocamlbuild -clean
	rm -f lib/*.a lib/*.cmxa lib/*.cmxs bin/* *.subdirs corestar_src
	$(MAKE) -C unit_tests clean
	$(MAKE) -C scripts clean
	$(MAKE) -C doc/tutorial clean

%.subdirs: %
	ls -F $*/ | grep / | sed "s./.." | sed "s.^.-I $*/." > $*.subdirs

corestar_src:
	ln -sf "$(CORESTAR_HOME)/src" corestar_src

.PHONY: build test test clean

-include .install.mk

#vim:noet:
