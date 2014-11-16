package casts.SwitchRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Object obj;
	
	int i = getInt();
	switch (i) {	
	case 1:
	    obj = new Foo();
	    break;
	case 7:
	    /*
	case 9:
	case 10:
	case 11:
	    */
	case 12:
	    obj = new String();
	case 13:
	case 15:
	    obj = new Object();
	    break;
	default:
	    obj = new Bar();
	}
	
	Foo f = (Foo) obj;
    }

    public static int getInt() {
	return 1;
    }
}