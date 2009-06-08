all:  Cell.jimple Recell.jimple DCell.jimple

%.class: %.java
	javac $?

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number

test: Cell.jimple Recell.jimple DCell.jimple
	./runtest Cell.jimple
	./runtest Recell.jimple
	./runtest DCell.jimple

clean: 
	rm -f *.jimple *.class *~ *.dot \#* .\#*