class Cell {
    int val;

    @Spec(
      pre="Val(this,_X)",
      post="Val(this,@p0:)"
    )
    void set(int x) {
	val = x;
    }

    @Spec(
      pre="Val(this,_X)",
      post="Val(this,_X) * return = _X"
    )
    int get() {
	return val;
    }
}