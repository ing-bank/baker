package webshop.simple;

import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ReservedItems;
import webshop.simple.ingredients.ShippingAddress;
import webshop.simple.ingredients.ShippingOrder;

public class MakePaymentInstance implements MakePayment {
    @Override
    public MakePaymentOutcome apply(String recipeInstanceId,
                                    ReservedItems reservedItems,
                                    ShippingAddress shippingAddress,
                                    PaymentInformation paymentInformation) {
        return new PaymentSuccessful(new ShippingOrder(reservedItems.getItems(), reservedItems.getDate(), shippingAddress));
    }
}
