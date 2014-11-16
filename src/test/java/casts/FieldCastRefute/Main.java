package casts.FieldCastRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Bar b = new Bar();
	Foo f = (Foo) b.f;
	b.writeF();
    }

    public static boolean getBool() {
	return true;
    }
}