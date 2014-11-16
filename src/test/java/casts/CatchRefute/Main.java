package casts.CatchRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Object x = new Object();
	int i = 0;
	try {
	    String y = (String) x;
	} catch (ClassCastException c) {}
    }

}
