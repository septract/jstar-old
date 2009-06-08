import java.util.Iterator;

public class IntegerSize implements Observer {

    private IntegerDataBag bag;
    private int size;

      public IntegerSize( IntegerDataBag bag ) {
            this.bag = bag;               
            bag.addObserver( this );
      }

      public void update( Subject o ) {
            if( o == bag ) {
		size = bag.list.size();
            }
      }
}
