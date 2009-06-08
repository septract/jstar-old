all: ConnectionPool.jimpl ResourcePool.jimple 

%.class: %.java
	javac $?

%.jimple: %.class
	java soot.Main $* -f J -d .

clean: 
	rm -f *.jimple *.class *~ *.dot

test: ResourcePool.jimple ConnectionPool.jimple
	./runtest ResourcePool.jimple
	./runtest ConnectionPool.jimple
