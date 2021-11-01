package webshop.simple;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;

public interface ShipItems extends Interaction {

    class ShippingConfirmed {}

    @FiresEvent(oneOf = {ShippingConfirmed.class})
    ShippingConfirmed apply(
            @RequiresIngredient("shippingAddress") ShippingAddress shippingAddress,
            @RequiresIngredient("reservedItems") ReservedItems reservedItems
    );
}
