package leaks.PathValueUpdateRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	//	localMap.increaseCapacity();
	localMap.put("a", new Act());
	//	storyCache.increaseCapacity();
	storyCache.put("b", new Object());
    }
}