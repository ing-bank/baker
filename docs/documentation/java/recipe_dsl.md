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