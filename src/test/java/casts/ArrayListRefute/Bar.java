package casts.ArrayListRefute;
import java.util.ArrayList;

public class Bar implements SimpleInterface {

    public ArrayList<SimpleInterface> f;

    public Bar() {
	this.f = new ArrayList<SimpleInterface>();//Foo();
	f.add(new Foo());
    }

    public void writeF() {
	f.add(new Bar());
    }

    public int getInt() {
	return 0;
    }

}