default: build test

build:
	cd src; make

scripts:
	cd scripts; make

test: build
	cd examples; make test

clean:
	rm -f lib/*.a
	cd src; make clean
	cd scripts; make clean
	cd examples; make clean
	cd doc/tutorial; make clean

#vim:noet:
