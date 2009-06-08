all: ResourceFactory.jimple ConnectionFactory.jimple ResourcePool.jimple 

%.class: %.java
	javac $?

%.jimple: %.class
	java soot.Main $* -f J -d .

clean: 
	rm -f *.jimple *.class *~

test: ResourcePool.jimple ConnectionFactory.jimple ResourceFactory.jimple
	./runtest ResourcePool.jimple
	./runtest ConnectionFactory.jimple
