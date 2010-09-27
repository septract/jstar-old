class DCell extends Cell {

    DCell() {
	super.set(super.get() + super.get());
    }
    void set(int y) {
	super.set(y+y);
    }

    int get() {
	return super.get();
    }

}