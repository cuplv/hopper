package casts.CatchRefuteInterproc;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {


    static Object global;

    public static void main(String[] args) {
	bar();
    }

   public static void foo(Object x) {
	global = new Object();
	x.toString();
	global = "a";
    }
    
    public static void bar() {
	Object x = null;
	try {
	    foo(x);
	} catch (NullPointerException e) {
	    global = "a";
	}	
	
	String y = (String) global;
    }
    
}
