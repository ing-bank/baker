# Recipe DSL

The recipe DSL allows you to declaritively describe your process.

Let's start with the [web shop](../index.md#visual-representation) recipe as an example.

The complete code example can be found [here](https://github.com/ing-bank/baker/blob/master/runtime/src/test/java/com/ing/baker/Webshop.java).

``` java
final Recipe webshopRecipe = new Recipe("webshop")
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
        new RetryWithIncrementalBackoffBuilder()
            .withInitialDelay(Duration.ofMillis(100))
            .withDeadline(Duration.ofHours(24))
            .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
            .build());
```

## Sensory events

[Events](concepts.md#event) are simple `POJO` classes. For example:

``` scala tab="Scala"
case class CustomerInfoReceived(customerInfo: CustomerInfo)

```

``` java tab="Java"
public class CustomerInfoReceived {
    public final CustomerInfo customerInfo;

    public CustomerInfoReceived(CustomerInfo customerInfo) {
        this.customerInfo = customerInfo;
    }
}
```

The field types of the `POJO` class must be compatible with the baker type system.

See the [supported types](type-system.md#default-supported-types) for more information.

The names of the fields are obtained using java reflection.

They can be added using the `.withSensoryEvents(..)` method.



### Firing limit

A *firing limit* is a limit on the number of times a sensory event may be received by a [process instance](dictionary.md#process-instance).

By default sensory events have a firing limit of `1` per process instance.

This means the event will be rejected with status `FiringLimitMet` after the first time it is received.

If you want to send an event more then once you may add it like this:

``` java
   .withSensoryEventsNoFiringLimit(CustomerInfoReceived.class)
```

In this example the `CustomerInfoReceived` can now be received multiple times by a process instance.

## Interactions

Interactions are interfaces with some requirements. See [here](interactions.md) how to define them.

You can include interactions in your recipe using the static `of(..)` method.

``` java
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

``` java
    .withInteractions(
        of(ShipGoods.class).withMaximumInteractionCount(1)
     )
```

### Predefining ingredients

An interaction normally requires all its input ingredients to be provided from [Events](concepts.md#event).

Sometimes however it is useful to *predefine* (or *hard code*) the value of an ingredient.

For example:

- An email template
- An application/requester id when calling an external system

This can be done by:

``` java
  .withInteractions(
    of(SendEmail.class)
      .withPredefinedIngredient("emailTemplate", "Welcome to ING!")
  )
```

Note that *predefined* ingredients are **always** available and do not have to be provided by an event for each interaction call.

Each time all *remaining* ingredients are provided, the interaction will fire.

You can **not** predefine *ALL* input ingredients of an interaction.

### Event requirements

As mentioned before, the DSL is declarative, you do not have to think about order. This is implicit in the data requirements of the interactions.

However, sometimes data requirements are not enough.

For example, you might want to be sure to only send an invoice (`SendInvoice`) *AFTER* the goods where shipped (`GoodsShipped`).

``` java
    of(SendInvoice.class)
        .withRequiredEvents(ShipGoods.GoodsShipped.class)
```

In this case the `GoodsShipped` event *MUST* happen before the interaction may execute.

You can specify multiple events in a single clause. These are bundled with an `AND` condition, meaning *ALL* events in the clause are required.

You can also require a single event from a number of options.

``` java
    of(SendInvoice.class)
        .withRequiredOneOfEvents(EventA.class, EventB.class)
```

In this case the interaction may fire if *either* `EventA` OR `EventB` has occured.

### Interaction Failure strategy

When an interaction throws an exception there are a number of mitigation strategies:

#### Fire event

This option is analagous to a `try { } catch { }` in code. When an exception is raised from the interaction you specify an
event to fire. So instead of failing the process continues.

Example:

``` java
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

``` java
  .withInteractions(
    of(ValidateOrder.class)
      .withFailureStrategy(new RetryWithIncrementalBackoffBuilder()
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