import java.util.LinkedList;
import java.util.Iterator;

public class IntegerDataBag implements Subject {

    public LinkedList list = new LinkedList();
    
    private LinkedList observers = new LinkedList();
    
    public void beginModification() { }

    public void endModification() { notifyObservers(); }

    public void addObserver( Observer o ) {
	observers.add( o );
	o.update(this);
    }

    public void removeObserver( Observer o ) {
	observers.remove( o );
    }

    private void notifyObservers() {
	// loop through and notify each observer
	Iterator i = observers.iterator();
	while( i.hasNext() ) {
	    Observer o = ( Observer ) i.next();
	    o.update( this );
	}
    }
}
