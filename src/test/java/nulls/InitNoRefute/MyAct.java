package nulls.InitNoRefute;

import android.app.Activity;
import android.os.Bundle;

public class MyAct extends Activity {

    public Object mObj;

    public MyAct() {
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
