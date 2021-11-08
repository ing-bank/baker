package webshop.simple;

import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;

public class MakePaymentInstance implements MakePayment {
    @Override
    public MakePaymentOutcome apply(String recipeInstanceId,
                                    ReservedItems reservedItems,
                                    PaymentInformation paymentInformation) {
        return new PaymentSuccessful();
    }
}
