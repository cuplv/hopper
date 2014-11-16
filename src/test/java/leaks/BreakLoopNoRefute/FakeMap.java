package leaks.BreakLoopNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String str, Object value) {
	//	table = new Object[capacity];
	Object o1 = new Object();
	Object o2 = new Object();
	int j = 0;
	for (int i = 0; i < 5; i++) {
	    j *= 3;
            if (o1 != null) {
		value = new Act();
		j--;
                break;
            } else if (o2 != null) {
		value = new Object();
		break;
	    } else {
		String s = new String("a");
		s.toString();
	    }

	    Object o3 = new Object();
	}	    
	table[size] = value;
	return null;
    }
}