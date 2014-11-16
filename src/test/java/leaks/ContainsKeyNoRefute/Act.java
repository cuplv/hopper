package leaks.ContainsKeyNoRefute;
import edu.colorado.thresher.external.Annotations.*;
import java.util.HashMap;
import java.util.Map;

@noStaticRef public class Act {

    int size;

    public Act() {}
    
    public static Map<String,Object> storyCache = new HashMap<String,Object>();

    public static void main(String[] args) {
	Map<String,Act> localMap = new HashMap<String,Act>();
	if (localMap.containsKey("b")) {
	    int boogalo = 3;
	}
	localMap.put("a", new Act());
	storyCache.put("b", new Act());
    }
}