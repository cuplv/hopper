package bounds.NestedOverflow3;
public class NestedOverflow3 {

    public static void main(String[] args) {
	foo(new int[3], new int[2]);
    }

    public static void foo(int[] buf1, int[] buf2) {
	for (int i = 0; i < buf1.length; i++) {
	    for (int j = 0; j < buf2.length; j++) { 
		buf1[i] = 2 * buf2[i];
	    }
	}
    }

}