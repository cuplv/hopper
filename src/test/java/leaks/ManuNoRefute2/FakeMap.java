package leaks.ManuNoRefute2;
public class FakeMap {
    public Bar f;
    public FakeMap() {}
    public static FakeMap makeFakeMap() { 
	return new FakeMap(); // o1
    }
}