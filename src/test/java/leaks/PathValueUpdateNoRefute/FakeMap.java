package leaks.PathValueUpdateNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = 2;
	size = -1;
    }

    public Object put(String i, Object value) {
	capacity = capacity / 2;
	if (size > capacity) table = new Object[capacity];
	table[size] = value;
	return null;
    }
}
