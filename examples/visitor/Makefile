all: Visitor.jimple Sum.jimple Plus.jimple Const.jimple Ast.jimple RZ.jimple

%.class: Visitor.java
	javac -g $?

%.jimple: %.class
	java soot.Main $* -f J -d . -print-tags -keep-line-number


clean: 
	rm -f *.jimple *.class *~ *.dot \#* .\#*

time:
	time ./runtest Const.jimple >/dev/null
	time ./runtest Plus.jimple >/dev/null
	time ./runtest RZ.jimple >/dev/null
	time ./runtest Sum.jimple >/dev/null

test: all
	./runtest Const.jimple
	./runtest Plus.jimple 
	./runtest RZ.jimple 
	./runtest Sum.jimple 

demo: RZ.jimple
	clear
	time ./runtest RZ.jimple