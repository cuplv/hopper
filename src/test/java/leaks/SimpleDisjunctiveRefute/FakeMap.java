package leaks.SimpleDisjunctiveRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    void bar() {}
    public int getInt(int i) { return i; }
    public int foo(int i) {

	do {
	    if(i == getInt(1) || i == getInt(2)) {
		bar();		
	    } else break;
	} while (true);
	return i;
    }

    public Object put(int i, Object value) {
	i = foo(i);

	if (i == 7 || i == 3 || i == 22) {
	    table = new Object[capacity];
	}
	table[size] = value;
	return null;
    }
}