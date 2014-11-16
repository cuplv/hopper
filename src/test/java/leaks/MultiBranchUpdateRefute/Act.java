package leaks.MultiBranchUpdateRefute;
import edu.colorado.thresher.external.Annotations.*;
@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	localMap.put("a", new Act(), 2);
	storyCache.put("b", new Object(), 5);
	//storyCache.put(new Object());

	FakeMap newMap = new FakeMap();
	newMap.put("5", new Object(), 3);
    }
}