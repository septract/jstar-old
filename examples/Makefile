ifndef TARGETS
  TARGETS =
endif

ifndef CLEAN
  CLEAN =  *.jimple *.class *~ *.dot \#* .\#* *.proof_file* 
endif 

ifndef SOURCES
  SOURCES =  $(addsuffix .java, $(TARGETS)) 
endif

ifndef SUBDIRSDEF
   SUBDIRSDEF = foo
   SUBDIRS = pool linkedlist popl2008 traditional multinh visitor subject
endif

ifndef DIR
   DIR = 
endif 

ifdef DIR
  INDENT := $(INDENT) " "
endif
export INDENT 

all: $(addsuffix .jimple, $(TARGETS)) 
	@for dir in ${SUBDIRS} ; do ( cd $$dir; make all ) ; done

test: all $(addsuffix .test, $(TARGETS)) $(addsuffix .test.dir, ${SUBDIRS})
	@echo

time :  all $(addsuffix .time, $(TARGETS))
	@for dir in ${SUBDIRS} ; do ( cd $$dir; make time ) ; done

%.class: $(SOURCES)
	javac -g $?

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number

%.test.dir: 
	@echo $(INDENT) Testing $(DIR); cd $*; make test

clean: 
	@for dir in ${SUBDIRS} ; do ( cd $$dir; make clean ) ; done
	@rm -f $(CLEAN)

%.time:
	@echo $(INDENT) Timing $(DIR)/$*
	@time ./runtest $*.jimple >/dev/null

%.test : %.jimple
	@echo $(INDENT) Testing $(DIR)/$*
	@./runtest $*.jimple
