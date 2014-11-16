package leaks.SingletonNoRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {

    private Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	Other other = Other.getInstance(new Act());
	localMap.put(1, other);
	storyCache.put(2, new Object());
	//storyCache.put(new Object());
    }
}