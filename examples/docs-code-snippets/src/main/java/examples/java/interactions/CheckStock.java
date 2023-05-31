package examples.java.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

import java.util.List;

public interface CheckStock extends Interaction {

    interface Outcome {
    }

    record OrderHasUnavailableItems(List<String> unavailableProductIds) implements Outcome {
    }

    record Success() implements Outcome {
    }

    @FiresEvent(oneOf = {Success.class, OrderHasUnavailableItems.class})
    Outcome apply(@RequiresIngredient("orderId") String orderId,
                  @RequiresIngredient("productIds") List<String> productIds
    );
}
