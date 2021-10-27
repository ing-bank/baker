package webshop.simple;

import com.ing.baker.recipe.javadsl.InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder;
import com.ing.baker.recipe.javadsl.Recipe;
import webshop.simple.ingredients.Item;
import webshop.simple.ingredients.PaymentInformation;
import webshop.simple.ingredients.ShippingAddress;

import java.time.Duration;
import java.util.List;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;

public class JWebshopRecipe {

    public static class OrderPlaced {

        public final String orderId;
        public final List<Item> items;

        public OrderPlaced(String orderId, List<Item> items) {
            this.orderId = orderId;
            this.items = items;
        }
    }

    public static class PaymentInformationReceived {
        public final PaymentInformation paymentInformation;

        public PaymentInformationReceived(PaymentInformation paymentInformation) {
            this.paymentInformation = paymentInformation;
        }
    }

    public static class ShippingAddressReceived {
        public final ShippingAddress shippingAddress;

        public ShippingAddressReceived(ShippingAddress shippingAddress) {
            this.shippingAddress = shippingAddress;
        }
    }

    public final static Recipe recipe = new Recipe("WebshopRecipe")
        .withSensoryEvents(
            OrderPlaced.class,
            PaymentInformationReceived.class,
            ShippingAddressReceived.class
        )
        .withInteractions(
            of(MakePayment.class),
            of(ReserveItems.class),
            of(ShipItems.class)
        )
        .withDefaultFailureStrategy(
            new RetryWithIncrementalBackoffBuilder()
                .withInitialDelay(Duration.ofMillis(100))
                .withDeadline(Duration.ofHours(24))
                .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
                .build()
        );
}
