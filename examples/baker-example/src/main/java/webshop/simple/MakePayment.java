package webshop.simple;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RecipeInstanceId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;

public interface MakePayment extends Interaction {

    interface MakePaymentOutcome { }

    class PaymentSuccessful implements MakePaymentOutcome { }

    class PaymentFailed implements MakePaymentOutcome { }

    @FiresEvent(oneOf = {PaymentSuccessful.class, PaymentFailed.class})
    MakePaymentOutcome apply(
            @RecipeInstanceId String recipeInstanceId,
            @RequiresIngredient("reservedItems") ReservedItems reservedItems,
            @RequiresIngredient("paymentInformation") PaymentInformation paymentInformation);
}
