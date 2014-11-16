package casts.CatchNoRefute;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

class Main {

    public static void main(String[] args) {
	Object x = new Object();
	int i = 0;
	String y = (String) x;
	try {
	    i++;
	} catch (ClassCastException c) {
	    i--;
	}
	i /= 1;
    }

}
