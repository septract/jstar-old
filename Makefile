default:
	cd src; make
	. setjstarenv; cd examples; make test

clean: 
	cd src; make clean
	cd examples; make clean