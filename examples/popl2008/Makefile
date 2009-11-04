all: Cell.jimple Recell.jimple DCell.jimple

%.class: Cell.java Recell.java D
	javac -g $?

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number


clean: 
	rm -f *.jimple *.class *~ *.dot \#* .\#* *.txt

time:
	time ./runtest Cell.jimple

test: all
	./runtest Cell.jimple
	./runtest Recell.jimple




demo: Cell.jimple
	clear
	time ./runtest Cell.jimple