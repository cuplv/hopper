package leaks.SimpleAliasingNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	Obj x;
	Obj z = new Obj(); // Obj0
	z.f = new Obj(); // Obj1
	if (rand()) {
	    x = new Obj(); // Obj2
	    z = x;
	} else {
	    x = new Obj(); // Obj3
	}
	x.f = new Act(); // Act0
	storyCache.put(1, z.f);
    }

    public static boolean rand() { return true; }

    static class Obj {
	public Object f;
	public Obj() {}
    }
}