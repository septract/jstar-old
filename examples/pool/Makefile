SUBDIRS = basic factory template


test: 
	@for i in $(SUBDIRS); do \
	echo "\nRunning tests in pool/"$$i ; \
	(cd $$i; make test); done

clean: 
	@for i in $(SUBDIRS); do \
	(cd $$i; make clean); done