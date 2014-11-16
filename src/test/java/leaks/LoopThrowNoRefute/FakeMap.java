package leaks.LoopThrowNoRefute;
public class FakeMap {

    private final static Object[] EMPTY_TABLE = new Object[1];
    private int size = 0;
    private int capacity;
    private Object[] table;

    public FakeMap() {
	table = EMPTY_TABLE;
	capacity = -1;
    }

    boolean replyPending;

    public Object put(String i, Object value, int count) {
	while (replyPending) {
	    replyPending = false;
	    if (count == 5) {
		throw new NullPointerException();
	    }
	}
	table[size] = value;
	return null;
    }

    public void bar() {
	int count = 0;
	while (count > 0) {
	    count--;
	    return;
	}
	foo(new Object());
    }


    public void foo(Object value) {
	table[size] = value;
    }
}