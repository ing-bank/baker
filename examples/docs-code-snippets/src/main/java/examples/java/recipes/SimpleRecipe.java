package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.OrderPlaced;
import examples.java.interactions.ShipItems;

public class SimpleRecipe {

    public final static Recipe recipe = new Recipe("example recipe")
        .withSensoryEvent(OrderPlaced.class)
        .withInteractions(
            InteractionDescriptor.of(ShipItems.class)
        );
}
