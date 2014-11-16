package leaks.LoopProcRefute;
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
	/*
	while (count > 0) {
	    count--;
	    table[size] = value;
	}
	*/

	table = new Object[count];
	for (int j = 0; j < 10; j++) {
	    foo(value);
	}


	return null;
    }

    private void foo(Object value) {
	table[size] = value;
    }
}