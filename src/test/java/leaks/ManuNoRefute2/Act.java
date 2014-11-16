package leaks.ManuNoRefute2;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {
    public Act() {}
    
    public static FakeMap storyCache;

    public static boolean nondet() {
	return false;
    }

    public static void main(String[] args) {
	storyCache = FakeMap.makeFakeMap();
	Bar w = Bar.makeBar();
        FakeMap y;
	Bar z;
	if (nondet()) {
	    y = new FakeMap(); // o3
	    z = Bar.makeBar();
	} else {
	    y = FakeMap.makeFakeMap();
	    z = new Bar(); // o4
	}
	storyCache.f = w;
	y.f = z;
	Act t = new Act(); // o5
	w.g = t;
    }
}