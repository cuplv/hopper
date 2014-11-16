package leaks.SimpleConjunctiveRefute;
import edu.colorado.thresher.external.Annotations.*;

@noStaticRef public class Act {
    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	storyCache.put(2, new Object());
	localMap.put(8, new Act());
    }
}