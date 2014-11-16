package leaks.FunctionCallRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String i, Object value) {
	doubleCapacity();
	table[size] = value;
	return null;
    }

    public void doubleCapacity() {
	table = new Object[capacity];
    }
}