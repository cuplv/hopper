package nulls;

import android.app.Activity;
import android.os.Bundle;

public class InitNoRefute extends Activity {

    public Object mObj;

    public InitNoRefute() {
	this.mObj = null;
    }

    @Override
    public void onCreate(Bundle b) {
	mObj.toString();
    }

    @Override
    public void onResume() {
	this.mObj = new Object();
    }
}
