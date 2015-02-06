package nulls.InitRefute;

import android.app.Activity;
import android.os.Bundle;

public class MyAct extends Activity {

    public Object mObj;

    public MyAct() {
	this.mObj = new Object();
    }

    @Override
    public void onCreate(Bundle b) {
	mObj.toString();
    }

}
