package casts.SwitchNoRefute;
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
	case 9:
	    obj = new Object();
	    break;
	default:
	    obj = new Bar();
	}
	
	Foo f = (Foo) obj;
    }

    public static int getInt() {
	return 7;
    }
}