package leaks.CheckCastNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {

    private Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	//	FakeMap localMap = new FakeMap();
	//	Other other = Other.getInstance(new Act());
	//	localMap.put(1, other);
	//	storyCache.put(2, new Object());
	Act a = getLocalInstance(1);
	//storyCache.put(new Object());
    }

    private static Act getLocalInstance(int i) {
	Act act = (Act) storyCache.get(i);
        if (act == null) {
            act = new Act();
	    storyCache.put(i, act);
        }

	return act;
    }
}