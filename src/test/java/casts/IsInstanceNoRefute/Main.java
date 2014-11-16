package casts.IsInstanceNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	SimpleInterface i;
	
	if (args[0] == "a") {
	    i = new Foo();
	} else {
	    i = new Bar();
	}

	Class c = Bar.class;
	if (c.isInstance(i)) {
	    Foo foo = (Foo) i;
	}
    }

}
