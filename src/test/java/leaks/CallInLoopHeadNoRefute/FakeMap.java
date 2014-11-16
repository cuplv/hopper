package leaks.CallInLoopHeadNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    public Object put(String str, Object value, int a, int b) {
	Object o1 = new Object();
	Object o2 = new Object();
	for (int i = 0; i < foo(i); i++) {
	    o1 = new Object();
        }
	table[size] = value;
	return null;
    }

    public int foo(int i) {
	if (i % 2 == 0) return i;
	else return 5;
    }
}