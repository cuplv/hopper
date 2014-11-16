package leaks.DoLoopRefute;
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
	table = new Object[3];
	do {
	    Object next = new Object();
	    count++;
	    if (count == 10) {
		//System.out.println("continuing");
		//count *= 2;
		//continue;
		count--;
	    }
	    count++;
	} while (count < 10);
	table[size] = value;
	  return null;
    }
}
