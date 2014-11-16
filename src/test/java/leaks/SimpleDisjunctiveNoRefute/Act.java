package leaks.SimpleDisjunctiveNoRefute;
import edu.colorado.thresher.external.Annotations.*;

@noStaticRef public class Act {
    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	localMap.put(9, new Act());
	storyCache.put(2, new Object());
	//storyCache.put(new Object());
    }
}