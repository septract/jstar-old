default: build test

build:
	cd src; make

test: build
	source setjstarenv; cd examples; make test

clean: 
	cd src; make clean
	cd examples; make clean
