package casts.FieldCastNoRefute;
public class Bar implements SimpleInterface {

    public SimpleInterface f;

    public Bar() {
	this.f = new Foo();
    }

    public void writeF() {
	this.f = new Bar();
    }

    public int getInt() {
	return 0;
    }

}