ifndef TARGETS
  TARGETS = OLIST
endif

ifndef CLEAN
  CLEAN =  *.proof_file* *.class *~ *.dot \#* .\#* 
endif

ifndef SUBDIRSDEF
   SUBDIRSDEF = foo
   SUBDIRS = 
endif

DIR = traditional/modelbased

include ../../Makefile

%.jimple:
	@echo Jimple file provided manually
