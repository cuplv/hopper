package leaks.InterproceduralRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
	size = 0;
    }

    public Object put(String i, Object value) {
	if (size > capacity) table = new Object[capacity];
	table[size++] = value;
	return null;
    }
}
