package casts.FieldCastNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Bar b = new Bar();
	b.writeF();
	Foo f = (Foo) b.f;
    }

    public static boolean getBool() {
	return true;
    }
}