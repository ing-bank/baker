package examples.java.recipes;

import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.FraudCheckCompleted;
import examples.java.events.OrderPlaced;
import examples.java.events.PaymentReceived;

public class RecipeWithSensoryEvents {

    public final static Recipe recipe = new Recipe("example")
        .withSensoryEventNoFiringLimit(OrderPlaced.class)
        .withSensoryEvent(PaymentReceived.class)
        .withSensoryEvent(FraudCheckCompleted.class, 5);
}
