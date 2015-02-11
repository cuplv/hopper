package nulls;

import android.app.Activity;
import android.os.Bundle;

public class InitRefute extends Activity {

    public Object mObj;

    public InitRefute() {
	this.mObj = new Object();
    }

    @Override
    public void onCreate(Bundle b) {
	mObj.toString();
    }

}
