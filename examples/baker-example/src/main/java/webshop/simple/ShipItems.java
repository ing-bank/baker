package webshop.simple;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RecipeInstanceId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;
import webshop.simple.ingredients.ShippingOrder;

public interface ShipItems extends Interaction {

    class ShippingConfirmed {}

    @FiresEvent(oneOf = {ShippingConfirmed.class})
    ShippingConfirmed apply(@RequiresIngredient("shippingOrder") ShippingOrder shippingOrder);
}
