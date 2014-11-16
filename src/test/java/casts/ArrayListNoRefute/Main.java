package casts.ArrayListNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Bar b = new Bar();
	b.writeF();
	Foo f = (Foo) b.f.get(0);
	b.writeF();
    }

    public static boolean getBool() {
	return true;
    }
}