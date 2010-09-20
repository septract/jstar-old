default: build test

build:
	cd src; make

scripts:
	cd scripts; make

test:
	cd unit_tests; make test

clean:
	rm -f lib/*.a
	cd src; make clean
	cd unit_tests; make clean
	cd scripts; make clean
	cd doc/tutorial; make clean

#vim:noet:
