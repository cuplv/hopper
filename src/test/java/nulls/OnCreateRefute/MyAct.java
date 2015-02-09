package nulls.OnCreateRefute;

import android.app.Activity;
import android.os.Bundle;

public class MyAct extends Activity {

    public Object mObj;

    @Override
    public void onCreate(Bundle b) {
	this.mObj = new Object();
    }

    @Override
    public void onDestroy() {
	mObj.toString();
    }

}
