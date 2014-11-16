package leaks.SubBranchRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	size = 0; 
	capacity = 0;
    }

    public Object put(String i, Object value) {
	if (size < capacity) {
	    foo();
	} else if (size == capacity) {
	    doubleCapacity();
	} else {
	    bar();
	}
	table[size] = value;
	return null;
    }

    private void doubleCapacity() {
	capacity = size * 2;
	table = new Object[capacity];
    }

    public void foo() {

    }

    public void bar() {

    }
}