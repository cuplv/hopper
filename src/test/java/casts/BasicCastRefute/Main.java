package casts.BasicCastRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	SimpleInterface i;
	if (getBool()) {
	    i = new Foo();
	} else {
	    i = new Bar();
	}	
	    
	Foo f = (Foo) i;
    }

    public static boolean getBool() {
	return true;
    }
}
