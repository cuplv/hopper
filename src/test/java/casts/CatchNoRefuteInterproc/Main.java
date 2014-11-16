package casts.CatchNoRefuteInterproc;
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
	} catch (NullPointerException e) {}	
	
	String y = (String) global;
    }
    
}
