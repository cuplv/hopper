package leaks.DoubleLoopRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	localMap.put("a", new Act(), 7);
	storyCache.put("b", new Object(), 7);
	//storyCache.put(new Object());
    }
}