package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;

public class ManualRetryInteraction {

    public void retryExample(Baker baker, String recipeInstanceId) {
        baker.retryInteraction(recipeInstanceId, "ShipOrder");
    }
}
