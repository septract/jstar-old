// From Kevin Bierhoff, Jonathan Aldrich, Modular Typestate Checking of
// Aliased Objects.
// The goal is to check that clients do not modify the underlying collection
// while iterating over it. Other legal operations should not result in bogus
// warnings. In particular, clients are allowed to acquire and use multiple
// iterators over the same collection.

interface Iterator {
  boolean hasNext();
  Object next();
}

interface Collection {
  void add(Object o);
  void remove(Object o);
  int size();
  Iterator iterator();
}

class List implements Collection {
  private static class Node {
    Object data;
    Node next;
    Node(Object data, Node next) {
      this.data = data;
      this.next = next;
    }
  }
  private static class LI implements Iterator {
    private Node next;
    LI(Node next) { this.next = next; }
    @Override public boolean hasNext() { return next != null; }
    @Override public Object next() {
      Object r = next.data;
      next = next.next;
      return r;
    }
  }
  private Node head;
  private Node tail;
  public List() {
    head = tail = new Node(null, null);
  }
  @Override public void add(Object o) {
    Node n = new Node(o, null);
    tail.next = n;
    tail = n;
  }
  @Override public int size() {
    int s;
    Node n;
    for (s = 0, n = head; n.next != null; n = n.next, ++s);
    return s;
  }
  @Override public Iterator iterator() { return new LI(head.next); }
  @Override public void remove(Object o) {
    tail = head;
    while (tail.next != null) {
      if (tail.next.data == o)
        tail.next = tail.next.next;
      else
        tail = tail.next;
    }
  }
}
