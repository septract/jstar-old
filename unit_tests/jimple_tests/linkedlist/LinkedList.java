class LinkedList
{
    private NodeLL head ;
    private NodeLL tail ;
    /* head == tail == null -> empty list */

    void create()
    {
	head=null;
	while (true) {
	    NodeLL n = new NodeLL() ;
	    n.next=head;
	    head=n;
	}
    }

    
    
    void reverseList()
    {
        NodeLL f = null ; // finished part of list
        NodeLL r = head ; // rest of list to do
        // swap head and tail
        NodeLL t = head ;
        head = tail ;
        tail = t ;
        // Assert: Loop Invariant: list is split
        //    between f and r, f being finished, r
        //    needs to be processed.
        while ( r!=null )
        {
           t = r ; // to process t
           r = r.next ; // loop will terminate :-)
           t.next = f ; // put on head
           f = t ; // note: t has been used
        }
    }
    
    
    void insertAtHead( String newString )
    {
        NodeLL n = new NodeLL() ;
        n.content = newString ;
        n.next = head ;
        head = n ;
        if ( tail==null ) tail = head ;
    }
    
    void insertAtTail( String newString )
    {
        if ( head==null )
        {
           insertAtHead( newString ) ;
        }
        else
        {
           NodeLL n = new NodeLL() ;
           n.content = newString ;
           tail.next = n ;
           tail = n ;
        }
    }

    
    void printList()
    {
        NodeLL n = head ;
        while ( n!=null )
        {
	    //        System.out.println(n.content) ;
            n = n.next ;
        }
    }

    
}


class NodeLL
{
    String content ;
    NodeLL next ;
}

