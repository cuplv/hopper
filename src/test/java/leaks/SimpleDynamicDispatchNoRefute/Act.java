package leaks.SimpleDynamicDispatchNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static Map storyCache = new FakeMap0();

    public static void main(String[] args) {
	Map localMap;
	if (nondet()) {
	    localMap = new FakeMap1();
	} else {
	    localMap = new FakeMap0();
	}
	localMap.put("a", new Act());
	storyCache.put("b", new Object());

	Map newMap = new FakeMap0();
	newMap.put("5", new Object());
    }

    public static boolean nondet() {
	return false;
    }
}