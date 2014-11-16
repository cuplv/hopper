package leaks.CallPruningNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	//	FakeMap localMap1 = new FakeMap();
	FakeMap localMap1 = null;
	doPutWrapper(2, new Object(), localMap1);
	localMap1 = new FakeMap();
	FakeMap localMap2 = new FakeMap();
	doPut(1, new Act(), localMap2);
	storyCache.put(2, new Object());
    }

    private static void doPut(int key, Object obj, FakeMap map) {
	map.put(key, obj);
    }

    private static void doPutWrapper(int key, Object obj, FakeMap map) {
	doPut(key, obj, map);
    }

	  
}