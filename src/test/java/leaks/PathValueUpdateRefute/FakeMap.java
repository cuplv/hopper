package leaks.PathValueUpdateRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = 0;
	size = -1;
    }

    public void increaseCapacity() {
	//capacity -= 2;
	capacity = -2 - capacity;
    }

    public Object put(String i, Object value) {
	capacity = -2 - capacity;
	if (size > capacity) table = new Object[capacity];
	table[size] = value;
	return null;
    }
}
