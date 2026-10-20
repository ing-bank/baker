package com.ing.baker;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RecipeInstanceId;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy;
import com.ing.baker.recipe.javadsl.Recipe;

import java.time.Duration;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;
import static org.mockito.Mockito.mock;

public class Webshop {

    public static class CustomerInfo {
        public final String name;
        public final String address;
        public final String email;

        public CustomerInfo(String name, String address, String email) {
            this.name = name;
            this.address = address;
            this.email = email;
        }
    }

    public static class OrderPlaced {
        public final String order;

        public OrderPlaced(String order) {
            this.order = order;
        }
    }

    public static class CustomerInfoReceived {
        public final CustomerInfo customerInfo;

        public CustomerInfoReceived(CustomerInfo customerInfo) {
            this.customerInfo = customerInfo;
        }
    }

    public interface ValidateOrder extends Interaction {

        interface Outcome {
        }

        class Failed implements Outcome {
        }

        class Valid implements Outcome {
        }

        @FiresEvent(oneOf = {Failed.class, Valid.class})
        Outcome apply(@RecipeInstanceId String recipeInstanceId, @RequiresIngredient("order") String key);
    }

    public interface ManufactureGoods extends Interaction {
        class GoodsManufactured {
            public final String goods;

            public GoodsManufactured(String goods) {
                this.goods = goods;
            }
        }

        @FiresEvent(oneOf = {GoodsManufactured.class})
        GoodsManufactured apply(@RequiresIngredient("order") String order);
    }

    public interface SendInvoice extends Interaction {

        class InvoiceWasSent {
        }

        @FiresEvent(oneOf = {InvoiceWasSent.class})
        InvoiceWasSent apply(@RequiresIngredient("customerInfo") CustomerInfo customerInfo);
    }

    public interface ShipGoods extends Interaction {

        class GoodsShipped {
            public final String trackingId;

            public GoodsShipped(String trackingId) {
                this.trackingId = trackingId;
            }
        }

        @FiresEvent(oneOf = {GoodsShipped.class})
        GoodsShipped apply(@RequiresIngredient("goods") String goods, @RequiresIngredient("customerInfo") CustomerInfo customerInfo);
    }

    public static class PaymentMade {
    }

    public final static Recipe webshopRecipe = new Recipe("webshop")
            .withSensoryEvents(
                    OrderPlaced.class,
                    CustomerInfoReceived.class,
                    PaymentMade.class)
            .withInteractions(
                    of(ValidateOrder.class),
                    of(ManufactureGoods.class)
                            .withRequiredEvents(PaymentMade.class, ValidateOrder.Valid.class),
                    of(SendInvoice.class)
                            .withRequiredEvents(ShipGoods.GoodsShipped.class),
                    of(ShipGoods.class))
            .withDefaultFailureStrategy(
                    new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                            .withInitialDelay(Duration.ofMillis(100))
                            .withDeadline(Duration.ofHours(24))
                            .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
                            .build());

    ShipGoods shipGoodsMock = mock(ShipGoods.class);
    SendInvoice sendInvoiceMock = mock(SendInvoice.class);
    ManufactureGoods manufactureGoodsMock = mock(ManufactureGoods.class);
    ValidateOrder validateOrderMock = mock(ValidateOrder.class);
}
