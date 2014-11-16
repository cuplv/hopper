package casts.HashtableEnumeratorNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Enumeration;
import java.util.Hashtable;

class Main {

    public static void main(String[] args) {
	Hashtable<SimpleInterface,String> either = new Hashtable<SimpleInterface,String>();
	either.put(new Bar(), "");
	either.put(new Foo(), "");
	Hashtable<Foo,String> foos = new Hashtable<Foo,String>();
	foos.put(new Foo(), "");
	
	for (Enumeration<SimpleInterface> e = either.keys(); e.hasMoreElements();) {
	    ((Bar)e.nextElement()).writeF(); // can fail
	}
	
	for (Enumeration<Foo> e = foos.keys(); e.hasMoreElements();) {
	    e.nextElement().getInt(); // is safe
	}
    }

    public static boolean getBool() {
	return true;
    }
}