package leaks.IndexSensitiveRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	localMap.put("a", new Act());
	storyCache.put("b", new Object());
    }
}