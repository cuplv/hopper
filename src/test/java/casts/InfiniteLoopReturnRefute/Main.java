package casts.InfiniteLoopReturnRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Object i;
	
	Object[] tbl = new Object[5];
	tbl[1] = new Object();
	Foo fs = new Foo();
	tbl[2] = fs;
	
	if (getBool(tbl, fs)) {
	    i = new Foo();
	} else if (getBool1()) {
	    i = new Bar();
	} else {
	    i = new Object();
	}

	if (i instanceof Foo) {
	    if (getBool(tbl, fs)) {
		Foo f = (Foo) i;
	    }
	}
    }

    public static boolean getBool(Object[] tbl, Object toFind) {
	int i = 0;
	while (true) {
	    Object item = tbl[i];
	    if (item == toFind) return true;
	    if (item == null) return false;
	    if (i == tbl.length - 1) return false;
	    i++;
	}
    }

    public static boolean getBool1() {
     return false;
    }
}