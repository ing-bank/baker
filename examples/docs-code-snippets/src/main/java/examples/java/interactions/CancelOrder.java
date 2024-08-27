package examples.java.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;

import java.util.List;

public interface CancelOrder extends Interaction {

    record OrderCancelled() {
    }

    @FiresEvent(oneOf = {OrderCancelled.class})
    OrderCancelled apply(@RequiresIngredient("orderId") String orderId,
                         @RequiresIngredient("unavailableProductIds") List<String> unavailableProductIds
    );
}
