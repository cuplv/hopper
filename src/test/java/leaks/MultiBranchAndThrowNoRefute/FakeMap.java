package leaks.MultiBranchAndThrowNoRefute;
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

    public Object nastyMethod(int a, int b, int c, int d, int e, Object value) {
	if (capacity >= size) {
	    throw new ArrayIndexOutOfBoundsException();
	} else if ((a == size ||
		    a == b ||
		    a == c ||
		    a == d) &&
		   capacity <= e) {
	    return value;
	} else {
	    throw new ArrayIndexOutOfBoundsException();
	}
    }

    public Object put(String i, Object value) {
	//	nastyMethod(1, 2, 3, 4, 5);
	value = nastyMethod(0, 0, 0, 0, 5, value);
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