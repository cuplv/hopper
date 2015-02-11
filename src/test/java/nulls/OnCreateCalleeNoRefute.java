package nulls;

import android.app.Activity;
import android.os.Bundle;

public class OnCreateCalleeNoRefute extends Activity {

    public Object mObj;
    public boolean doInit = false;

    @Override
    public void onCreate(Bundle b) {	
	if (doInit) initialize();
    }

    private void initialize() {
	this.mObj = new Object();
    }

    @Override
    public void onDestroy() {
	mObj.toString();
    }

}
