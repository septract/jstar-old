ifndef TARGETS
  TARGETS = CELL BCELL
endif

ifndef SUBDIRSDEF
   SUBDIRSDEF = foo
   SUBDIRS = 
endif

DIR = traditional/cells

include ../../Makefile

%.jimple:
	@echo Jimple file provided manually

clean:
	@for dir in ${SUBDIRS} ; do ( cd $$dir; make clean ) ; done
	@rm -f *.class *~ *.dot \#* .\#* *.proof_file*
