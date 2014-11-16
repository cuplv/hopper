package leaks.SimpleDynamicDispatchNoRefute;
public class FakeMap0 implements Map {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size;
    private int capacity;
    private Object[] table;

    public FakeMap0() {
	table = EMPTY_TABLE;
	size = 0; 
	capacity = 0;
    }

    public Object put(String i, Object value) {
	table[size] = value;
	return null;
    }
}