package leaks.CheckCastNoRefute;
public class FakeMap {
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = new Object[2];//EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(int i, Object value) {

	table[size] = value;
	return null;
    }

    public Object get(int i) {
	return table[i];
    }
}