package casts.HashtableEnumeratorRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Enumeration;
import java.util.Hashtable;

class Main {

    public static void main(String[] args) {
	Hashtable<Bar,String> bars = new Hashtable<Bar,String>();
	bars.put(new Bar(), "");
	Hashtable<Foo,String> foos = new Hashtable<Foo,String>();
	foos.put(new Foo(), "");
	
	for (Enumeration<Bar> e = bars.keys(); e.hasMoreElements();) {
	    e.nextElement().writeF();
	}
	
	for (Enumeration<Foo> e = foos.keys(); e.hasMoreElements();) {
	    e.nextElement().getInt();
	}
    }

    public static boolean getBool() {
	return true;
    }
}