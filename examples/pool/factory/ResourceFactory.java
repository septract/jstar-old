import java.util.*;

public interface ResourceFactory<R,E extends Exception> {

    public R makeResource() throws E;

    public void destructResource(R r) throws E;

}
