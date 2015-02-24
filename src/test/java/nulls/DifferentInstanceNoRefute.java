package nulls;

import android.app.Activity;
import android.os.Bundle;

public class DifferentInstanceNoRefute extends Activity {

    public static Object sObj = new Object();
    public Object mObj;


    @Override
    public void onCreate(Bundle b) {
	this.sObj.toString();
    }

    @Override
    public void onDestroy() {
	this.sObj = null;
    }

}
