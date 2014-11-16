package leaks.MultiBranchUpdateRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	size = 0; 
	capacity = -1;
    }

    public Object put(String i, Object value, int count) {
	size = 0;
	capacity = 3;

	if (count == 3) {
	    size += 2;
	} else {
	    capacity += 1;
	}
	
	if (size < capacity) {
	    doubleCapacity();
	} else if (size == capacity) {
	    foo();
	} else {
	    bar();
	}
	table[size] = value;
	return null;
    }

    private void doubleCapacity() {
	table = new Object[capacity];
    }

    public void foo() {
    }

    public void bar() {
    }
}