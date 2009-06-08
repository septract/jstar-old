class Recell extends Cell {
    int bak;

    void set(int x) {
	bak = super.get();
	super.set(x);
    }

    int get() {
	return super.get();
    }

}