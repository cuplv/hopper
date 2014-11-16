package leaks.SimpleConjunctiveNoRefute;
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
	boolean test = i > 3 && i < 5  && i == 5;
	if (test) table = new Object[capacity];
	table[size] = value;

	boolean t0 = test || true;
	return null;
    }
}