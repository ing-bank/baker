package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.events.OrderPlaced;
import examples.java.interactions.CancelOrder;
import examples.java.interactions.CheckStock;
import examples.java.interactions.ShipOrder;

public class WebShopRecipe {

    public final static Recipe recipe = new Recipe("web-shop recipe")
        .withSensoryEvent(OrderPlaced.class)
        .withInteractions(
            InteractionDescriptor.of(CheckStock.class),
            InteractionDescriptor.of(ShipOrder.class)
                .withRequiredEvent(CheckStock.SufficientStock.class),
            InteractionDescriptor.of(CancelOrder.class)
                .withRequiredEvent(CheckStock.OrderHasUnavailableItems.class)
        );
}
