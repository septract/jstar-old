// See IC.java.

public class Client {
  public static void main(String[] args) {
    Collection c = new List();
    c.add(3);
    Iterator i = c.iterator();
    while (i.hasNext()) {
      Object o = i.next();
      Iterator j = c.iterator();
      while (j.hasNext()) {
        Object p = j.next();
      }
    }
    if (i.hasNext() && c.size() == 3) {
      c.remove(i.next());
      if (i.hasNext()) {;}
    }
    Iterator k = c.iterator();
  }
}
