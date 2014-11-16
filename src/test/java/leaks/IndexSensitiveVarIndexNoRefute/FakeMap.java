package leaks.IndexSensitiveVarIndexNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    private int[] ints = new int[5];

    public FakeMap() {
	table = EMPTY_TABLE;
	ints[1] = 2;
	ints[2] = 1;
    }

    public Object put(int i, Object value) {
	if (ints[i] > 2) table = new Object[capacity];
	Object[] objs = table;
	table[size++] = value;
	return null;
    }
}