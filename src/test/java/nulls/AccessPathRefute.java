package nulls;

import android.app.Activity;
import android.os.Bundle;

public class AccessPathRefute extends Activity {

    static class Helper {
	public Object mObj;
	
	public void attach() {
	    this.mObj = new Object();
	}
    }

    Helper mHelper;

    @Override
    public void onCreate(Bundle b) {
	mHelper = new Helper();
	mHelper.attach();
    }

    @Override
    public void onDestroy() {
	mHelper.mObj.toString();
    }

}
