package nulls;

import android.app.Activity;
import android.content.ComponentCallbacks;
import android.content.res.Configuration;
import android.os.Bundle;

public class CbNoRefute extends Activity {

    public Object mObj;

    @Override
    public void onCreate(Bundle b) {
	this.mObj = new Object();
	registerComponentCallbacks(new ComponentCallbacks() {
		@Override
		public void onConfigurationChanged(Configuration newConfig) {
		    mObj.toString();
		}
		
		@Override
		public void onLowMemory() {}

	    });
    }

    @Override
    public void onResume() {
	this.mObj = null;
    }

}
