package leaks.ForEachLoopRefute;
import java.util.List;
import java.util.LinkedList;

public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value, List<Object> objs) {

	table = new Object[5];
	
	for (Object obj : getObjs(FakeMap.class)) {
	    Object o = bar();
	    if (o != null) {
		int j = 17;
		j++;
	    }
	    table[size] = obj;
	}
	foo(value);
	return null;
    }

    public static List<Object> getObjs(Class c) {
	List<Object> objs = new LinkedList<Object>();
	objs.add(new Object());
	return objs;
    }

    private Object bar() { return new Object(); }

    private void foo(Object value) {
	table[size] = value;
    }
}