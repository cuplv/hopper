package leaks.SharedStaticMapNoRefute;
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

    public Object put(String i, Object value) {
	table[size] = value;
	return null;
    }
}
