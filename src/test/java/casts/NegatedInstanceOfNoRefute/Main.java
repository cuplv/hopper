package casts.NegatedInstanceOfNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	SimpleInterface i;

	Foo fs = new Foo();
	
	if (getBool()) {
	    i = new Foo();
	} else {
	    i = new Bar();
	}

	if (!(i instanceof Foo)) {
	    Foo f = (Foo) i;
	}
    }

    public static boolean getBool() {
	return false;
    }
}