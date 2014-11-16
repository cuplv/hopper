package leaks.ForEachLoopArrRefute;
import edu.colorado.thresher.external.Annotations.*;
import java.util.LinkedList;
import java.util.List;

@noStaticRef public class Act {


    public Act() {}
    
    public static FakeMap storyCache = new FakeMap();

    public static void main(String[] args) {
	FakeMap localMap = new FakeMap();
	List<Object> objs = new LinkedList<Object>();
	objs.add(new Object());
	localMap.put("a", new Act(), objs);
	storyCache.put("b", new Object(), objs);
	//storyCache.put(new Object());
    }
}