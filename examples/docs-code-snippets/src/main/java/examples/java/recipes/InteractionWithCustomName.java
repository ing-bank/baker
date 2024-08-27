package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.interactions.ShipOrder;

public class InteractionWithCustomName {

    public final static Recipe recipe = new Recipe("example")
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class, "ship-order")
        );
}
