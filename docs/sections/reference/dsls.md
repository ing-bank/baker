# Recipe DSLs

Conceptually a `Recipe` allows you to declaratively describe your business process and is a "blueprint" that can be used to
start a `RecipeInstance` on the runtime. To create such "blueprint" you need to use either the Java or Scala DSLs, there
a `Recipe` is just a data structure that bundles `Events`, `Interactions` and some execution configuration like firing limits
or error handling mechanics.

_Note: `Ingredients` are indirectly added to the `Recipe` because they come inside `Events`._

These data structures are just that, data, and to ease their construction and improve the user experience of the library
we provide an API that uses Java and Scala reflection to generate most of the data from language constructions like case 
classes or interfaces.

=== "Scala"

    ```scala 
    import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
    import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
    import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

    import scala.concurrent.duration._

    object WebshopRecipe {

      val recipe: Recipe = Recipe("Webshop")
        .withSensoryEvents(
          Events.OrderPlaced,
          Events.PaymentMade)
        .withInteractions(
          Interactions.ReserveItems
            .withRequiredEvent(Events.PaymentMade))
        .withDefaultFailureStrategy(
          RetryWithIncrementalBackoff
            .builder()
            .withInitialDelay(100 milliseconds)
            .withUntil(Some(UntilDeadline(24 hours)))
            .withMaxTimeBetweenRetries(Some(10 minutes))
            .build())

      object Ingredients {

        val OrderId: Ingredient[String] =
          Ingredient[String]("orderId")

        val Items: Ingredient[List[String]] =
          Ingredient[List[String]]("items")

        val ReservedItems: Ingredient[List[String]] =
          Ingredient[List[String]]("reservedItems")

        val UnavailableItems: Ingredient[List[String]] =
          Ingredient[List[String]]("unavailableItems")
      }

      object Events {

        val OrderPlaced: Event = Event(
          name = "OrderPlaced",
          providedIngredients = Seq(
            Ingredients.OrderId,
            Ingredients.Items
          ),
          maxFiringLimit = Some(1)
        )

        val PaymentMade: Event = Event(
          name = "PaymentMade",
          providedIngredients = Seq.empty,
          maxFiringLimit = Some(1)
        )

        val OrderHadUnavailableItems: Event = Event(
          name = "OrderHadUnavailableItems",
          providedIngredients = Seq(
            Ingredients.UnavailableItems
          ),
          maxFiringLimit = Some(1)
        )

        val ItemsReserved: Event = Event(
          name = "ItemsReserved",
          providedIngredients = Seq(
            Ingredients.ReservedItems
          ),
          maxFiringLimit = Some(1)
        )
      }

      object Interactions {

        val ReserveItems: Interaction = Interaction(
          name = "ReserveItems",
          inputIngredients = Seq(
            Ingredients.OrderId,
            Ingredients.Items,
          ),
          output = Seq(
            Events.OrderHadUnavailableItems,
            Events.ItemsReserved
          )
        )
      }
    }
    ```

=== "Scala (Reflection API)"

    ```scala 

    import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
    import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
    import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe}

    import scala.concurrent.duration._

    object WebshopRecipeReflection {

      case class OrderPlaced(orderId: String, items: List[String])

      case class PaymentMade()

      sealed trait ReserveItemsOutput

      case class OrderHadUnavailableItems(unavailableItems: List[String]) extends ReserveItemsOutput

      case class ItemsReserved(reservedItems: List[String]) extends ReserveItemsOutput

      val ReserveItems = Interaction(
        name = "ReserveItems",
        inputIngredients = Seq(
          Ingredient[String]("orderId"),
          Ingredient[List[String]]("items")
        ),
        output = Seq(
          Event[OrderHadUnavailableItems],
          Event[ItemsReserved]
        )
      )

      val recipe: Recipe = Recipe("Webshop")
        .withSensoryEvents(
          Event[OrderPlaced],
          Event[PaymentMade])
        .withInteractions(
          ReserveItems
            .withRequiredEvent(Event[PaymentMade]))
        .withDefaultFailureStrategy(
          RetryWithIncrementalBackoff
            .builder()
            .withInitialDelay(100 milliseconds)
            .withUntil(Some(UntilDeadline(24 hours)))
            .withMaxTimeBetweenRetries(Some(10 minutes))
            .build())
    }

    ```

=== "Java (Reflection API)"

    ```java 

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
    ```

## Events

[Events](../../reference/main-abstractions/#event-and-eventinstance) are simple `POJO` classes. For example:

=== "Scala"

    ```scala 
    case class CustomerInfoReceived(customerInfo: CustomerInfo)
    ```
    
=== "Java"

    ```java 
    public class CustomerInfoReceived {
        public final CustomerInfo customerInfo;

        public CustomerInfoReceived(CustomerInfo customerInfo) {
            this.customerInfo = customerInfo;
        }
    }
    ```

The field types of the `POJO` class must be compatible with the baker type system.

See the [supported types](../../reference/baker-types-and-values/#primitives) for more information.

The names of the fields are obtained using reflection.

They can be added using the `.withSensoryEvents(..)` method.



### Firing limit

A *firing limit* is a limit on the number of times a sensory event may be received by a 
[recipe instance](../../reference/main-abstractions/#recipe-and-recipeinstance).

By default sensory events have a firing limit of `1` per process instance.

This means the event will be rejected with status `FiringLimitMet` after the first time it is received.

If you want to send an event more then once you may add it like this:

```java
   .withSensoryEventsNoFiringLimit(CustomerInfoReceived.class)
```

In this example the `CustomerInfoReceived` can now be received multiple times by a process instance.

## Interactions

Interactions are interfaces with some requirements. See [here](../../development-life-cycle/design-a-recipe/#interactions) how to define them.

You can include interactions in your recipe using the static `of(..)` method.

```java
import static com.ing.baker.recipe.javadsl.InteractionDescriptor.of;

final Recipe webshopRecipe = new Recipe("webshop")
    .withInteractions(
        of(ValidateOrder.class)
    )
```

There are a number of options to tailor an interaction for your recipe.

### Maximum interaction count

By default there is *no* limit on the number of times an Interaction may fire.

Sometimes you may want to set a limit.

For example, to ensure the goods are shipped only once.

```java
    .withInteractions(
        of(ShipGoods.class).withMaximumInteractionCount(1)
     )
```

### Predefining ingredients

An interaction normally requires all its input ingredients to be provided from [Events](../../reference/main-abstractions/#event-and-eventinstance).

Sometimes however it is useful to *predefine* (or *hard code*) the value of an ingredient.

For example:

- An email template
- An application/requester id when calling an external system

This can be done by:

```java
  .withInteractions(
    of(SendEmail.class)
      .withPredefinedIngredient("emailTemplate", "Welcome to ING!")
  )
```

Note that *predefined* ingredients are **always** available and do not have to be provided by an event for each interaction call.

Each time all *remaining* ingredients are provided, the interaction will fire.

You can **not** predefine *ALL* input ingredients of an interaction.

### Event renames

Sometimes it useful to rename an interaction event and/or its ingredients to fit better in the context of your recipe.

For example, to rename the `GoodsManufactured` event and its ingredient.

```java
  .withInteractions(
    of(ManufactureGoods.class)
      .withEventTransformation(
        GoodsManufactured.class, "ManufacturingDone",
        ImmutableMap.of("goods", "manufacturedGoods")
      )
    )
  )
```

### Event requirements

As mentioned before, the DSL is declarative, you do not have to think about order. This is implicit in the data requirements of the interactions.

However, sometimes data requirements are not enough.

For example, you might want to be sure to only send an invoice (`SendInvoice`) *AFTER* the goods where shipped (`GoodsShipped`).

```java
    of(SendInvoice.class)
        .withRequiredEvents(ShipGoods.GoodsShipped.class)
```

In this case the `GoodsShipped` event *MUST* happen before the interaction may execute.

You can specify multiple events in a single clause. These are bundled with an `AND` condition, meaning *ALL* events in the clause are required.

You can also require a single event from a number of options.

```java
    of(SendInvoice.class)
        .withRequiredOneOfEvents(EventA.class, EventB.class)
```

In this case the interaction may fire if *either* `EventA` OR `EventB` has occured.

### Interaction Failure strategy

When an interaction throws an exception there are a number of mitigation strategies:

#### Block interaction

This is the *DEFAULT* strategy if no other is defined and no [default strategy](#default-failure-strategy) is defined.

This option is suitable for non idempotent interactions that cannot be retried.

When an exception is thrown from the interaction the interaction is *blocked*.

This means that the interaction cannot execute again automatically.

It requires [manual intervening](../../development-life-cycle/resolve-failed-recipe-instances/) to continue the process from then on.

#### Fire event

This option is analagous to a `try { } catch { }` in code. When an exception is raised from the interaction you specify an
event to fire. So instead of failing the process continues.

Example:

```java
  .withInteractions(
    of(ValidateOrder.class)
    .withInteractionFailureStrategy(
       InteractionFailureStrategy.FireEvent("ValidateOrderFailed")
     )
   )
```

#### Retry with incremental backoff

Incremental backoff allows you to configure a retry mechanism that takes longer for each retry.
The idea here is that you quickly retry at first but slower over time. To not overload your system but give it time to recover.

```java
  .withInteractions(
    of(ValidateOrder.class)
      .withDefaultFailureStrategy(new RetryWithIncrementalBackoffBuilder()
        .withInitialDelay(Duration.ofMillis(100))
        .withBackoffFactor(2.0)
        .withMaxTimeBetweenRetries(Duration.ofSeconds(100))
        .withDeadline(Duration.ofHours(24))
        .build())
  )
```

What do these parameters mean?

| name | meaning |
| --- | --- |
| `initialDelay` | The delay for the first retry. |
| `backoffFactor` | The backoff factor for the delay (optional, `default = 2`) |
| `maxTimeBetweenRetries` | The maximum interval between retries. |
| `deadLine` | The maximum total amount of time spend delaying. |

For our example this results in the following delay pattern:

`100 millis` -> `200 millis` -> `400 millis` -> `...` ->  `100 seconds` -> `100 seconds`

Which can be visualized like this:

![](/images/incremental-backoff.png)

Note that these delays do **not** include interaction execution time.

For example, if the first retry execution takes `5` seconds (and fails again) then the second retry will
be triggered after (from the start):

`(100 millis + 5 seconds + 200 millis) = 5.3 seconds`

This also means that the `24 hour` deadline **does not** include interaction execution time. It is advisable to take this
into account when coming up with this number.

**Retry exhaustion**

It can happen that after some time, when an interaction keeps failing, that the retry is exhausted.

When this happens 2 things may happen.

Either the interaction becomes [blocked(#blocked-interaction).

Or if you configure so, the process continues with a predefined event:

```java
.withDefaultFailureStrategy(new RetryWithIncrementalBackoffBuilder()
  .withFireRetryExhaustedEvent(SomeEvent.class))

```

Note that this event class **requires** an empty constructor to be present and **cannot** provide ingredients.

## Default failure strategy

You can also define a default failure strategy on the recipe level.

This then serves as a fallback if none is defined for an interaction.

For example:

```java
final Recipe webshopRecipe = new Recipe("webshop")
    .withDefaultFailureStrategy(
        new RetryWithIncrementalBackoffBuilder()
            .withInitialDelay(Duration.ofMillis(100))
            .withDeadline(Duration.ofHours(24))
            .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
            .build());
```

