
default:
	export PATH=`echo $PATH`:`pwd`/bin
	cd src; make
	cd examples; make test