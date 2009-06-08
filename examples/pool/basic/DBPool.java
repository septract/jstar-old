import java.util.*;
import java.sql.*;

class DBPool {
    LinkedList<Connection> conns;
    String url;
    String user;
    String password;

    DBPool(String url,String user, String password) { 
	conns = new LinkedList<Connection>();
	this.url = url;
	this.user = user;
	this.password = password;
    }

    public Connection getResource() throws SQLException {
	if(conns.size() == 0) 
	    return DriverManager.getConnection(url,user,password);
	return conns.removeFirst();
    }

    public void freeResource(Connection db) throws SQLException {
	if(conns.size() >= 20) 
	    db.close();
	else 
	    conns.add(db);
    }


}