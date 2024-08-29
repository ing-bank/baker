package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;

public class ManualResolveInteraction {

    public void resolveExample(Baker baker, String recipeInstanceId) {
        baker.resolveInteraction(
            recipeInstanceId,
            "ShipOrder",
            EventInstance.from("ShippingFailed")
        );
    }
}
