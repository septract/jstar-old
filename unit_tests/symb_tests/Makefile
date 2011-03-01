TESTS=$(wildcard *_test)

test: $(TESTS)

$(TESTS): %_test:
	@${JSTAR_HOME}/bin/jstar -f $*_test -l $*_logic -a $*_abs > $*.out 2> $*.err || echo -e "\nFailed $* in $(CURDIR) (see $*.out and $*.err)"

clean:
	rm -f *.dot *proof_file*txt *.err *.out

.PHONY: test clean $(TESTS)
