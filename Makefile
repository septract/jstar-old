default: build test

build:
	cd src; make

test:
	cd examples; make test

clean: 
	cd src; make clean
	cd examples; make clean
	cd doc/tutorial; make clean
	rm -f lib/*
#vim:noet:
