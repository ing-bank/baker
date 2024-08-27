package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;

public class ManualStopInteraction {

    public void stopExample(Baker baker, String recipeInstanceId) {
        baker.stopRetryingInteraction(recipeInstanceId, "ShipOrder");
    }
}
