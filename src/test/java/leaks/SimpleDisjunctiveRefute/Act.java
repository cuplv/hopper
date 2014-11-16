package leaks.SimpleDisjunctiveRefute;
import edu.colorado.thresher.external.Annotations.*;

@noStaticRef public class Act {
    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	localMap.put(3, new Act());
	storyCache.put(19, new Object());
	//storyCache.put(new Object());
    }
}