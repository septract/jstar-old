class DCell extends Cell {
    
    void set(int y) {
	super.set(y+y);
    }

    int get() {
	return super.get();
    }

}