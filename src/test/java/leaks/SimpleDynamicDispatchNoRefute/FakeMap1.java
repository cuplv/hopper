package leaks.SimpleDynamicDispatchNoRefute;
public class FakeMap1 implements Map {

    //    private final static Object[] EMPTY_TABLE = new Object[0];
    private final static Object[] FUN_TABLE = new Object[1];
    private int size;
    private int capacity;
    private Object[] table;

    public FakeMap1() {
	//	table = EMPTY_TABLE;
	table = FUN_TABLE;
	size = 0; 
	capacity = 0;
    }

    public Object put(String i, Object value) {
	table = new Object[5];
	table[size] = value;
	return null;
    }
}