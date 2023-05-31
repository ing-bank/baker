package examples.java.interactions;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import examples.java.ingredients.Address;

public interface ShipOrder extends Interaction {

    record Success() {
    }

    @FiresEvent(oneOf = {Success.class})
    Success apply(@RequiresIngredient("orderId") String orderId,
                  @RequiresIngredient("address") Address address
    );
}
