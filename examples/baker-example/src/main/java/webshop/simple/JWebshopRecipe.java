package webshop.simple;

import com.ing.baker.recipe.javadsl.InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder;
import com.ing.baker.recipe.javadsl.Recipe;
import webshop.simple.ingredients.Item;
import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ShippingAddress;

import java.time.Duration;
import java.util.List;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static webshop.simple.MakePayment.*;

public class JWebshopRecipe {

    public static class OrderPlaced {

        public final List<Item> items;

        public OrderPlaced(List<Item> items) {
            this.items = items;
        }
    }

    public static class PaymentInformationReceived {
        private final PaymentInformation paymentInformation;

        public PaymentInformationReceived(PaymentInformation paymentInformation) {
            this.paymentInformation = paymentInformation;
        }

        public PaymentInformation getPaymentInformation() {
            return paymentInformation;
        }
    }

    public static class ShippingAddressReceived {
        private final ShippingAddress shippingAddress;

        public ShippingAddressReceived(ShippingAddress shippingAddress) {
            this.shippingAddress = shippingAddress;
        }

        public ShippingAddress getShippingAddress() {
            return shippingAddress;
        }
    }

    public final static Recipe recipe =
    new Recipe("WebshopRecipe")
        .withInteractions(
            of(MakePayment.class),
            of(ReserveItems.class),
            of(ShipItems.class)
                .withRequiredEvent(PaymentSuccessful.class)
        )
        .withSensoryEvents(
            OrderPlaced.class,
            PaymentInformationReceived.class,
            ShippingAddressReceived.class
        );
}
