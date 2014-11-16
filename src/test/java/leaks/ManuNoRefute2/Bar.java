package leaks.ManuNoRefute2;
public class Bar {
    public Act g;
    public Bar() {}
    public static Bar makeBar() {
	return new Bar(); // o2
    }
}