package casts.InstanceOfRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Object i;

	Foo fs = new Foo();
	
	if (getBool()) {
	    i = new Foo();
	} else if (getBool1()) {
	    i = new Bar();
	} else {
	    i = new Object();
	}

	if (i instanceof Foo) {
	    Foo f = (Foo) i;
	} 
    }

    public static boolean getBool() {
       return false;
    }

    public static boolean getBool1() {
       return false;
    }
}