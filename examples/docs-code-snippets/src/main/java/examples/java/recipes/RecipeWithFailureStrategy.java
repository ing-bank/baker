package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.interactions.ShipOrder;

public class RecipeWithFailureStrategy {

    public final static Recipe recipe = new Recipe("example")
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class)
                .withFailureStrategy(
                        InteractionFailureStrategy.FireEvent("shippingFailed")
                )
        );
}
