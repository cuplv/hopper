package leaks.BranchReturnRefute;
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
	if (i == 7) {
	    i = 6;
	    table = new Object[capacity];
	} else if (i == 2) {
	    i = 5;
	} else if (i == 1) return null;
	else i = 4;

	int j = i + 1;
	table[size] = value;
	return null;
    }
}