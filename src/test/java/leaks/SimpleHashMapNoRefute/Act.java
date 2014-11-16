package leaks.SimpleHashMapNoRefute;
import edu.colorado.thresher.external.Annotations.*;
import java.util.HashMap;
import java.util.Map;

@noStaticRef public class Act {

    public Act() {}
    
    public static Map<String,Object> storyCache = new HashMap<String,Object>();

    public static void main(String[] args) {
	Map<String,Object> localMap = new HashMap<String,Object>();
	storyCache.put("b", new Act());
	localMap.put("a", new Object());
    }
}