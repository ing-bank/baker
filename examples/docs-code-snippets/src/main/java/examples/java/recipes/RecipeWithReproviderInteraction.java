package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.OrderPlaced;
import examples.java.interactions.ShipOrder;

public class RecipeWithReproviderInteraction {

    public final static Recipe recipe = new Recipe("Reprovider recipe")
        .withSensoryEvent(OrderPlaced.class)
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class)
                    .isReprovider(true)
                    .withRequiredEvent(OrderPlaced.class)
        );
}
