package bounds.SwitchedBufsOverflow;
public class SwitchedBufsOverflow {

    public static void main(String[] args) {
	int[] buf1 = new int[11], buf2 = new int[10];
	foo(buf1, buf2);
    }

    public static void foo(int[] buf1, int[] buf2) {
	for (int i = 0; i < buf1.length; i++) {
	    buf2[i] = 7;
	}
    }

}