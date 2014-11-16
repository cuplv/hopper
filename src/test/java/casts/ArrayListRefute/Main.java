package casts.ArrayListRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Bar b = new Bar();
	Foo f = (Foo) b.f.get(0);
	b.writeF();
    }

    public static boolean getBool() {
	return true;
    }
}