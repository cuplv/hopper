package leaks.ContainsKeyRefute;
import edu.colorado.thresher.external.Annotations.*;
import java.util.HashMap;
import java.util.Map;

@noStaticRef public class Act {

    int size;

    public Act() {}
    
    public static Map<String,Object> storyCache = new HashMap<String,Object>();

    public static void main(String[] args) {
	Map<String,Object> localMap = new HashMap<String,Object>();
	if (localMap.containsKey("b")) {
	    localMap.put("b", new Object());
	}

	localMap.put("a", new Act());
	//storyCache.put("b", new Object());
	//storyCache.put("b", new Act());
	//storyCache.put(new Object());
    }
}