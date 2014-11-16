package casts.HashtableEnumeratorRefute;
import java.util.ArrayList;

public class Bar implements SimpleInterface {

    //public ArrayList<Foo> f;

    public Bar() {
	//this.f = new ArrayList<Foo>();
	//f.add(new Foo());
    }

    public void writeF() {
	//f.add(new Bar());
    }

    public int getInt() {
	return 0;
    }

    //public ArrayList<Foo> getF() { return f; }

}