package leaks.ForEachLoopArrRefute;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Collection;


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
	//String[] strs1 = new String[3];
	/*
	String[] strs2 = new String[3];

	try {
	    Object o3 = bar();
	    for (String str1 : strs1) {
		Object o2 = bar();
		for (String str2 : strs2) {
		    Object o = bar();
		    if (o != null) {
			int j = 17;
			j++;
		    }
		    table[size] = str2;
		}
	    }
	    Object o4 = new Object();
	} catch (Exception e) {
	    
	}
	*/

	String[] strs1 = getStringArr();

	Collection<String> retval =  new ArrayList<String>(strs1.length);
  
	for (String str1 : strs1) {
	    if (str1.equals("6")) {
		retval.add(str1);
	    }
	}

	
	if (retval.size() > 2) foo(value);


	return null;
    }

    private String[] getStringArr() {
	return new String[5];
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