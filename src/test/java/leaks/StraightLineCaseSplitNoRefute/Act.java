package leaks.StraightLineCaseSplitNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {
   
    public Act() { }
    
    public static Node storyCache = new Node();
  
    public static void main(String[] args) {
	Node a = new Node();
	Node b = a;
	Node c = b;
	Node d = c;
	d.next = a;
	d.data = new Act();
	Node e = c.next;
	storyCache.data = e.data;
    }

    /*
y = new()
z = a
a = y
{y -> u^, u^.f -> v^} || {y -> u^, z ->w^ * a->x^ }
z.f = a
{y -> u^, u^.f -> v^} (u^ from pt(y), v^ from pt(y.f))
x = y.f
{x -> v^}
    */

}