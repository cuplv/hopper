package nulls;

import android.app.Activity;
import android.os.Bundle;

public class OnCreateCalleeRefute extends Activity {

    public Object mObj;

    @Override
    public void onCreate(Bundle b) {
	initialize();
    }

    private void initialize() {
	this.mObj = new Object();
    }

    @Override
    public void onDestroy() {
	mObj.toString();
    }

}
