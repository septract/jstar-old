JSTAR_CMD = jstar
TEST_CMD = testharness
JAVA_CMD = java

JSTAR_OPTS = -v -dot
TEST_OPTS = -v

BASE_DIR = $(shell pwd)

JIMPLE_DIR_NAME = jimple
TESTS_DIR_NAME = tests
LOGIC_DIR_NAME = logic

SPEC_FILE_NAME = LinkedList.specs
LOGIC_FILE_NAME = LinkedList.logic
ABS_FILE_NAME = LinkedList.abs

JIMPLE_DIR = $(BASE_DIR)/$(JIMPLE_DIR_NAME)
TRACES_DIR = $(BASE_DIR)/traces
TESTS_DIR = $(BASE_DIR)/$(TESTS_DIR_NAME)
LOGIC_DIR = $(BASE_DIR)/$(LOGIC_DIR_NAME)

SPEC_FILE = $(BASE_DIR)/$(SPEC_FILE_NAME)
LOGIC_FILE = $(BASE_DIR)/$(LOGIC_FILE_NAME)
ABS_FILE = $(BASE_DIR)/$(ABS_FILE_NAME)

CLASSES = java.lang.Object java.util.AbstractCollection java.util.AbstractSequentialList java.util.LinkedList java.util.LinkedList$$Entry java.util.LinkedList$$Iter

LOGIC_FILES = dseg
TESTS = $(addsuffix .test, $(LOGIC_FILES))

.SUFFIXES: .jimple .test
.PRECIOUS: %.jimple

default: java.util.LinkedList
.PHONY: default

all: $(CLASSES)
.PHONY: all

clean:
	-rm -fr $(JIMPLE_DIR)/* &> /dev/null
	-rm -f $(BASE_DIR)/execution.dot &> /dev/null
	-rm -f $(BASE_DIR)/icfg.dot &> /dev/null
	-rm -rf $(TRACES_DIR)/*
.PHONY: clean

test: $(TESTS)
.PHONY: test

%.jimple:
	$(JAVA_CMD) soot.Main -f jimple $(*F) -d $(JIMPLE_DIR)

%: $(JIMPLE_DIR)/%.jimple
	mkdir -p $(TRACES_DIR)/$(*F)
	cd $(TRACES_DIR)/$(*F); \
	$(JSTAR_CMD) $(JSTAR_OPTS) -l $(LOGIC_FILE) -a $(ABS_FILE) -s $(SPEC_FILE) -f $(JIMPLE_DIR)/$@.jimple

%.test:
	$(TEST_CMD) $(TEST_OPTS) -l $(LOGIC_DIR)/$*.logic -f $(TESTS_DIR)/$@
