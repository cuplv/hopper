package leaks.StartInLoopNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value, int count) {
	while (count > 0) {
	    count--;
	    table[size] = value;
	}
	return null;
    }
}