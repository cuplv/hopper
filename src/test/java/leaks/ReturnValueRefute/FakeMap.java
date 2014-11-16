package leaks.ReturnValueRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    public FakeMap() {
	table = EMPTY_TABLE;
	//	capacity = -1;
	//	size = 0;
    }

    public Object put(String i, Object value) {
	//	capacity = -1;
	//size = 0;
	//size = 0;
	if (size > callMe()) table = new Object[capacity];
	//if (size > capacity) table = new Object[capacity];
	Object[] objs = table;
	table[size++] = value;
	return null;
    }

    private int callMe() {
	return -1;
	//return 1;
    }
}