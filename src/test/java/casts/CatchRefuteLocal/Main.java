package casts.CatchRefuteLocal;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {


    static Object global;

    public static void main(String[] args) {
	bar();
    }

    public static void bar() {
	global = new Object();
	Object x = null;
	try {
	    x.toString();
	    global = "a";
	} catch (NullPointerException e) {
	    global = "b";
	}	

	String y = (String) global;
    }

}
