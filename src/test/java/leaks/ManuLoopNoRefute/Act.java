package leaks.ManuLoopNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {
   
    public Act() { }
    
    public static Node storyCache = new Node();
  
    public static void main(String[] args) {
	Node x = new Node();
	Node head = x;
	for (int i = 0; i < 3; i++) {
	    x.next = new Node();
	    x = x.next;
	}
	x.data = new Act();
	Node a = head;
	Node b = a.next;
	Node c = b.next;
	Node e = c.next;
	storyCache.data = e.data;
    }
    
}