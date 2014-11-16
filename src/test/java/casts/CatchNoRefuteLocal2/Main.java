package casts.CatchNoRefuteLocal2;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {


    static Object global;

    public static void main(String[] args) {	
	bar(new Object());
    }

    public static void bar(Object x) {
	try {
	    x.toString();
	    global = new Object();
	} catch (NullPointerException e) {
	    global = "a";
	}	

	String y = (String) global;
    }

}
