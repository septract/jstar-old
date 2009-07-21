PATH:=$(PATH):`pwd`/bin

JSTAR_LOGIC_LIBRARY = `pwd`/library/logic
JSTAR_ABS_LIBRARY = `pwd`/library/abstraction
JSTAR_SPECS_LIBRARY = `pwd`/library/specs

default:
	cd src; make
	export JSTAR_LOGIC_LIBRARY="$(JSTAR_LOGIC_LIBRARY)"; export PATH="$(PATH)"; cd examples; make test

clean: 
	cd src; make clean
	cd examples; make clean