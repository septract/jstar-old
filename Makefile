default: build test

build:
	cd src; make

test:
	cd examples; make test

clean:
	rm -f lib/*.a
	cd src; make clean
	cd examples; make clean
	cd doc/tutorial; make clean

#vim:noet:
