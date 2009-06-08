all: DBPool.jimple 

%.class: %.java
	javac $?

%.jimple: %.class
	java soot.Main $* -f J -d .

clean: 
	rm -f *.jimple *.class *~ *.dot \#* .\#*

test: DBPool.jimple
	./runtest DBPool.jimple