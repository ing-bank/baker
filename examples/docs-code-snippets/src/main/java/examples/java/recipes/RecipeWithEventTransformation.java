package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.OrderPlaced;
import examples.java.interactions.ShipOrder;

public class RecipeWithEventTransformation {

    public final static Recipe recipe = new Recipe("example")
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class)
                .withEventTransformation(OrderPlaced.class, "OrderCreated")
                .renameRequiredIngredient("customerId", "userId")
                .renameRequiredIngredient("productIds", "skus")
        );
}
