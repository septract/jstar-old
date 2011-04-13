ifndef CORESTAR_HOME
	CORESTAR_HOME=$(CURDIR)/../corestar
endif
export CORESTAR_HOME

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

.PHONY: build test test clean

-include .install.mk

#vim:noet:
