all:  LinkedList.jimple NodeLL.jimple

%.class: LinkedList.java
	javac $?

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number

test: all
	./runtest LinkedList.jimple

clean: 
	rm -f *.jimple *.class *~ *.dot \#* .\#*