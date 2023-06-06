package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.FraudCheckCompleted;
import examples.java.interactions.ShipOrder;

public class RecipeWithRequiredEvents {

    public final static Recipe recipe = new Recipe("example")
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class)
                .withRequiredEvent(FraudCheckCompleted.class)
                .withRequiredOneOfEventsFromName("PaymentReceived", "UsedCouponCode")
        );
}
