import java.util.*;

public abstract class ResourcePool<R,E extends Exception> {

    LinkedList<R> resources;

    ResourcePool() { resources = new LinkedList<R>(); }

    abstract protected R makeResource() throws E;

    abstract protected void destructResource(R r) throws E;

    public R getResource() throws E{
	if(resources.size() == 0) {
	    return makeResource();
	}
	return resources.removeFirst();
    }

    public void freeResource(R r) throws E {
	if(resources.size() >= 20) {
	    destructResource(r);
	} else {
	    resources.add(r);
	}
    }
}
