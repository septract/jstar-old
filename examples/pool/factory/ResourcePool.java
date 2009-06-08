import java.util.*;

public class ResourcePool<R,E extends Exception> {

    LinkedList<R> resources;
    ResourceFactory<R,E> rf;

    ResourcePool(ResourceFactory<R,E> rf) { 
	resources = new LinkedList<R>(); 
	this.rf = rf;
    }

    public R getResource() throws E{
	if(resources.size() == 0) {
	    return rf.makeResource();
	}
	return resources.removeFirst();
    }

    public void freeResource(R r) throws E {
	if(resources.size() >= 20) {
	    rf.destructResource(r);
	} else {
	    resources.add(r);
	}
    }
}
