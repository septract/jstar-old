SUBDIRS = popl2008 pool visitor linkedlist subject


test: 
	@for i in $(SUBDIRS); do \
	echo "\nRunning tests in" $$i ; \
	(cd $$i; make test); done

clean: 
	@for i in $(SUBDIRS); do \
	(cd $$i; make clean); done