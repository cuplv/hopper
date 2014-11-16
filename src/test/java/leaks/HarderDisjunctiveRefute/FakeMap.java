package leaks.HarderDisjunctiveRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(int i, Object value) {
	if (i == 7 || i == 3) {
	    while (i < 7) {
	    table = new Object[capacity];
	    }
	}
	table[size] = value;
	return null;
    }
}