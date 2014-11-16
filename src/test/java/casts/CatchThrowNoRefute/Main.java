package casts.CatchThrowNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {


    static Object global;

    public static void foo() throws MyException {
	global = new Object();
	throw new MyException();
    }

    public static void main(String[] args) {
	try {
	    foo();
	    global = "a";
	} catch (MyException e) {
	}
	
	String y = (String) global;
    }

}
