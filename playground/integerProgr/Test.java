public class Test {

    boolean random() { return true; /* Spec doesn't specify return, so prover considers result random*/}

    boolean f () {
	int x = 0;
	int n = 0;
	while(random()) { n++; x++; } 
	return x==n;
    }

}