package nulls;

import android.app.Activity;
import android.os.Bundle;

public class OnCreateNoRefute extends Activity {

    public Object mObj;

    @Override
    public void onCreate(Bundle b) {
	mObj = new Object();
    }

    @Override
    public void onResume() {
	mObj = null;
    }

    @Override
    public void onDestroy() {
	mObj.toString();
    }

}
