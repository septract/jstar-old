build:
	$(MAKE) -C src

test: build
	$(MAKE) -s -C unit_tests

doc:
	$(MAKE) -C doc/tutorial

scripts:
	$(MAKE) -C scripts

all: test scripts doc

clean:
	rm -f lib/*.a
	$(MAKE) -C src clean
	$(MAKE) -C unit_tests clean
	$(MAKE) -C scripts clean
	$(MAKE) -C doc/tutorial clean

.PHONY: build test test clean

#vim:noet:
