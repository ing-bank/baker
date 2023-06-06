package examples.java.recipes;

import com.ing.baker.recipe.javadsl.CheckPointEvent;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.FraudCheckCompleted;
import examples.java.events.PaymentReceived;

public class RecipeWithCheckpointEvent {

    public final static Recipe recipe = new Recipe("example")
        .withCheckpointEvent(
            new CheckPointEvent("CheckpointReached")
                .withRequiredEvents(
                        PaymentReceived.class,
                        FraudCheckCompleted.class
                )
        );
}
