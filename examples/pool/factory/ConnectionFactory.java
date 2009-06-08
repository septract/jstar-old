import java.sql.*;

class ConnectionFactory implements ResourceFactory<Connection,SQLException> {

    String url, user, password;

    ConnectionFactory(String url, String user, String password) {
	this.url = url;
	this.user = user;
        this.password = password;
    }

    public Connection makeResource() throws SQLException {
	return DriverManager.getConnection(url,user,password);
    }

    public void destructResource(Connection c) throws SQLException {
	c.close();
    }
}