# Recipe DSL

Let's take the web shop recipe as an example.

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

## Predefining ingredients

An interaction normally requires its input ingredients to be delivered from [Events](../concepts#event).

Sometimes however it is useful to *predefine* (or *hard code*) the value of an ingredient.

For example:

- The template of an email
- An application/requester id when calling an external system

This can be accomplished by:

``` java
  .withInteractions(
    of(SendEmail.class)
      .withPredefinedIngredient("emailTemplate", "Welcome to ING!")
  )
```

Note that *predefined* ingredients are **always** available and do not have to be provided by an event for each interaction call.

Each time all *remaining* ingredients are provided, the interaction will fire.

You cannot predefine *all* input ingredients of an interaction.


## Interaction Failure strategy

When an interaction throws an exception there are a number of mitigation strategies:

### Fire event

This option is analagous to a try/catch in code. When an exception is raised from the interaction you may specify an
event to fire.

Example:

``` java
  .withInteractions(
    of(ValidateOrder.class).withInteractionFailureStrategy

```

### Retry

``` java
  .withInteractions(
    of(ValidateOrder.class)
      .withDefaultFailureStrategy(new RetryWithIncrementalBackoffBuilder()
        .withInitialDelay(Duration.ofMillis(100))
        .withBackoffFactor(2.0)
        .withMaxTimeBetweenRetries(Duration.ofMinutes(10))
        .withDeadline(Duration.ofHours(24))
        .build())
  )
```

What do these parameters mean?

| name | meaning |
| --- | --- |
| `initialDelay` | The delay for the 1st retry |
| `backoffFactor` | The multiplication factor for the delay (optional, default = 2) |
| `maxTimeBetweenRetries` | The maximum delay |
| `deadLine` | The total amount of time spend delaying |


So in our example the interaction will be retried after an initial delay of `100` milleseconds and a default backoff factor of `2.0`.

This results in the following retry pattern:

`100 millis -> 200 millis -> 400 millis -> ... ->  10 minutes -> 10 minutes`

Note that these delays are *after* interaction completion.

So for example, if the initial delay is `100` milleseconds and the execution takes `5` seconds then the second retry will
be triggered after (from the start):

`(100 millis + 5 seconds + 200 millis) = 5.3 seconds`

This also means that the `24 hour` deadline **does not** include interaction execution time. It is advisable to take this
into account when coming up with this number.