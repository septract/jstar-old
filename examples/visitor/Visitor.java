interface Visitor {
    public void visitC(Const x);
    public void visitP(Plus p);
}

interface Ast {
    public void accept(Visitor v);
}

class Const implements Ast{
    int v;

    Const(int x) { this.v = x; }
    
    public void accept(Visitor v) {
	v.visitC(this);
    }      
}

class Plus implements Ast {
    Ast left,right;

    Plus(Ast l, Ast r) {
	left = l;
	right = r;
    }

    public void accept(Visitor v) {
	v.visitP(this);
    }
}


class Sum implements Visitor{
    int amount; 
    public void visitP(Plus x) {
	x.left.accept(this);
        x.right.accept(this);
    }

    public void visitC(Const x) {
	amount += x.v;
    }
}

class RZ implements Visitor {
    boolean isZero;
    boolean isChanged;
    Ast newl;

    public void visitC(Const c) {
	if(c.v==0) {
	    this.isZero = true;
	}
    }

    public void visitP(Plus p) {
	p.left.accept(this);
	if(this.isZero) {
	    this.isZero = false;
	    this.isChanged = false;
	    p.right.accept(this);
	    if(!isChanged) {
		this.newl = p.right;
		isChanged = true;
	    }
	} else {
	    if(this.isChanged) {
		p.left = this.newl;
		this.isChanged = false;
	    }
	    p.right.accept(this);
	    if(this.isZero) {
		this.newl = p.left;
		this.isChanged = true;
		this.isZero = false;
	    } else if (this.isChanged) {
		p.right = this.newl;
		this.isChanged = false;
	    }
	}
    }

    Ast test1() {
	Ast a = new Plus(new Const(0), new Const(0));
	RZ rz = new RZ();
	a.accept(rz);
	if(rz.isChanged)
	    return rz.newl;
	else 
	    return a;
    }

}
