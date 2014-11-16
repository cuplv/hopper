package casts.IteratorRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

class Main {

    public static void main(String[] args) {
	List<Object> objs = new ArrayList<Object>();
	objs.add(new Object());
	List<Bar> bars = new ArrayList<Bar>();
	bars.add(new Bar());
	List<Foo> foos = new ArrayList<Foo>();
	foos.add(new Foo());

	for (Bar bar : bars) {
	    bar.writeF();
	}
	
	for (Foo foo : foos) {
	    int i = foo.getInt();
	    i++;
	}

	for (Object obj : objs) {
	    obj.hashCode();
	}

	Bar bar = bars.get(0);
	Foo foo = foos.get(0);
    }

    public static boolean getBool() {
	return true;
    }
}