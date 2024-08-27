package examples.java.recipes;

import com.ing.baker.recipe.javadsl.InteractionDescriptor;
import com.ing.baker.recipe.javadsl.Recipe;
import examples.java.interactions.ShipOrder;

import java.math.BigDecimal;
import java.util.Map;

public class RecipeWithPredefinedIngredients {

    public final static Recipe recipe = new Recipe("example")
        .withInteractions(
            InteractionDescriptor.of(ShipOrder.class)
                .withPredefinedIngredients(
                    Map.of(
                        "shippingCostAmount", new BigDecimal("5.75"),
                        "shippingCostCurrency", "EUR"
                    )
                )
        );
}
