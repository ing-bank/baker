package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.OrderPlaced;
import examples.java.interactions.ShipOrder;

public class SimpleRecipe {

    public final static Recipe recipe = new Recipe("example recipe")
        .withSensoryEvent(OrderPlaced.class)
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class)
        );
}
