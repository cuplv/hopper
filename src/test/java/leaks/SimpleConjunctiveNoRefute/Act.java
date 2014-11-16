package leaks.SimpleConjunctiveNoRefute;
import edu.colorado.thresher.external.Annotations.*;

@noStaticRef public class Act {
    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	storyCache.put(5, new Object());
	localMap.put(8, new Act());
    }
}