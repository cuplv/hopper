package bounds.BufParamOverflow;
public class BufParamOverflow {

    public static void main(String[] args) {
	int[] buf = new int[10];
	foo(buf);
    }

    public static void foo(int[] buf) {
	for (int i = 0; i <= buf.length; i++) {
	    buf[i] = 7;
	}
    }

}