package leaks.MultiLevelParamPassNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private Object[] table;
    private int capacity;
    private int size;

    public FakeMap() {
	table = EMPTY_TABLE;
    }

    public Object putty(int j, Object value) {
	if (j != 7) {
	    Object[] objs = table;
	    table[size++] = value;
	}
	return null;
    }


    public Object put(int i, Object value) {
	return putty(i, value);
    }
}