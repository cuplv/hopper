package nulls;

import android.app.Activity;
import android.os.Bundle;

public class UncommonLifecycleCallbackRefute extends Activity {

    public Object mObj;

    @Override
    public void onCreate(Bundle b) {
	this.mObj = new Object();
    }

    @Override 
    public void onBackPressed() {
	mObj.toString();	
    }

}
