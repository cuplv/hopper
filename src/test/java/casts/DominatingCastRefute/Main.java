package casts.DominatingCastRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    SimpleInterface i;

    public static void main(String[] args) {
	new Main().m();
    }

    public void m() {
	if (getBool()) {
	    this.i = new Foo();
	} else {
	    this.i = new Bar();
	}

	Foo f1 = (Foo) this.i;	
	Foo f2 = (Foo) this.i;
    }

    public static boolean getBool() {
	return false;
    }
}
