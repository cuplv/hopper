package leaks.SingletonNoRefute;
public class Other {

    private Act act;

    private static Other instance;

    private Other(Act act) { this.act = act; }

    public static Other getInstance(Act act) {
	if (instance == null) {
	    instance = new Other(act);
	}
	return instance;
    }
}