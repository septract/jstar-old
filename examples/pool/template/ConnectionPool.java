import java.sql.*;

class ConnectionPool extends ResourcePool<Connection,SQLException> {

    String url;
    String user;
    String password;

    ConnectionPool(String url, String user, String password) {
	this.url = url;
	this.user = user;
        this.password = password;
    }

    protected Connection makeResource() throws SQLException {
	return DriverManager.getConnection(url,user,password);
    }

    protected void destructResource(Connection c) throws SQLException {
	c.close();
    }
   
    /*  Just here to trick the verification into checking inherited methods */
    public void freeResource(Connection r) throws SQLException { super.freeResource(r); }
    public Connection getResource() throws SQLException { return super.getResource(); }
}