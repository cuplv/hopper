package leaks.ArrayLengthRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[22];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value) {
	if (table.length > 10) table = new Object[5];
	table[size] = value;
	return null;
    }
}