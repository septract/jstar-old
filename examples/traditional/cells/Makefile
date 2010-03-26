ifndef TARGETS
  TARGETS = CELL BCELL
endif

ifndef CLEAN
  CLEAN = *.proof_file* *.class *~ *.dot \#* .\#*
endif

ifndef SUBDIRSDEF
   SUBDIRSDEF = foo
   SUBDIRS = 
endif

DIR = traditional/cells

include ../../Makefile

%.jimple:
	@echo Jimple file provided manually
