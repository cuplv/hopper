package leaks.IndexSensitiveDefaultValRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    private Object[] objs = new Object[5];

    public FakeMap() {
	table = EMPTY_TABLE;
	objs[2] = new Object();
    }

    public Object put(String i, Object value) {
	if (objs[1] == null) table = new Object[capacity];
	Object[] objs = table;
	table[size++] = value;
	return null;
    }
}