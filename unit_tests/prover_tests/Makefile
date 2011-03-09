TESTS=$(wildcard *_test)

test: $(TESTS)

$(TESTS): %_test:
	@${JSTAR_HOME}/bin/test_logic -f $*_test -l $*_logic > $*.out 2> $*.err || echo -e "\nFailed $* in $(CURDIR) (see $*.out and $*.err)"

clean:
	rm -rf *.out *.err

.PHONY: test clean $(TESTS)
