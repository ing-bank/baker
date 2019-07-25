package webshop.simple;

import com.ing.baker.recipe.annotations.FiresEvent;
import com.ing.baker.recipe.annotations.RequiresIngredient;
import com.ing.baker.recipe.javadsl.InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder;
import com.ing.baker.recipe.javadsl.Interaction;
import com.ing.baker.recipe.javadsl.Recipe;

import java.time.Duration;
import java.util.List;

import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;

public class JWebshopRecipe {

    public static class OrderPlaced {

        public final String orderId;
        public final List<String> items;

        public OrderPlaced(String orderId, List<String> items) {
            this.orderId = orderId;
            this.items = items;
        }
    }

    public static class PaymentMade {}

    public interface ReserveItems extends Interaction {

        interface ReserveItemsOutcome {
        }

        class OrderHadUnavailableItems implements ReserveItemsOutcome {

            public final List<String> unavailableItems;

            public OrderHadUnavailableItems(List<String> unavailableItems) {
                this.unavailableItems = unavailableItems;
            }
        }

        class ItemsReserved implements ReserveItemsOutcome {

            public final List<String> reservedItems;

            public ItemsReserved(List<String> reservedItems) {
                this.reservedItems = reservedItems;
            }
        }

        @FiresEvent(oneOf = {OrderHadUnavailableItems.class, ItemsReserved.class})
        ReserveItemsOutcome apply(@RequiresIngredient("orderId") String id, @RequiresIngredient("items") List<String> items);
    }

    public final static Recipe recipe = new Recipe("WebshopRecipe")
        .withSensoryEvents(
            OrderPlaced.class,
            PaymentMade.class)
        .withInteractions(
            of(ReserveItems.class)
                .withRequiredEvent(PaymentMade.class))
        .withDefaultFailureStrategy(
            new RetryWithIncrementalBackoffBuilder()
                .withInitialDelay(Duration.ofMillis(100))
                .withDeadline(Duration.ofHours(24))
                .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
                .build());
}
