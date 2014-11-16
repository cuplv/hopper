package leaks.BranchRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
    }

    public Object put(String i, Object value) {
	int size = 0;
	int capacity = -1;
	if (size > capacity) table = new Object[capacity];
	//	else table = new Object[capacity];
	table[size++] = value;
	return null;
    }
}