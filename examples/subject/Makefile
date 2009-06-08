all:  IntegerDataBag.jimple IntegerSize.jimple Subject.jimple Observer.jimple

%.class: %.java
	javac -Xlint:unchecked $?

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number 

test: all
	./runtest IntegerSize.jimple
	./runtest IntegerDataBag.jimple

clean: 
	rm -f *.jimple *.class *~ *.dot \#* .\#*