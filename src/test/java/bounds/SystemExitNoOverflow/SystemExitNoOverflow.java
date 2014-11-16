package bounds.SystemExitNoOverflow;
public class SystemExitNoOverflow {

    public static void main(String[] args) {
	for (int i = 0; i < args.length; i++) {
	    if (args[i] == "-classpath") {
		if (++i >= args.length) usage();

		String classpath = args[i];
	    } else {
		String s = args[i];
	    }
	} 
    }

    private static void usage() {
	System.err.println("Usage message");
	System.exit(0);
    }

}