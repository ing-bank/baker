# Resolve Failed Recipes

## Interaction Failure strategy

When an interaction throws an exception there are a number of mitigation strategies:

## Block interaction

This is the *DEFAULT* strategy if no [default strategy](#default-failure-strategy) is defined.

This option is suitable for non idempotent interactions that cannot be retried.

When an exception is thrown from the interaction the interaction is *blocked*.

This means that the interaction cannot execute again automatically.

## Fire event

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

## Retry with incremental back-off

Incremental back-off allows you to configure a retry mechanism that takes longer for each retry.
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
| `backoffFactor` | The back-off factor for the delay (optional, `default = 2`) |
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



## baker.retryInteraction(recipeInstanceId, interactionName)

It is possible that during the execution of a `RecipeInstance` it becomes *blocked*, this can happen either because it 
is `directly blocked` by an exception (and the `FailureStrategy` of the `Interaction` of the `Recipe` was set to block) 
or that the retry strategy was exhausted. At this point it is possible to resolve the blocked interaction in 2 ways. 
This one involves forcing another try, resulting either on a successful continued process, or again on a failed state, 
to check this you will need to request the state of the `RecipeInstance` again.

_Note: this behaviour can be automatically preconfigured by using the `RetryWithIncrementalBackoff` `FailureStrategy`
on the `Interaction` of the `Recipe`_

=== "Scala"

    ```scala 
    val program: Future[Unit] = 
        baker.retryInteraction(recipeInstanceId, "ReserveItems")
    ```

=== "Java"

    ```java 
    CompletableFuture<BoxedUnit> program = 
        baker.retryInteraction(recipeInstanceId, "ReserveItems");
    ```

## baker.resolveInteraction(recipeInstanceId, interactionName, event)

It is possible that during the execution of a `RecipeInstance` it becomes *blocked*, this can happen either because it 
is `directly blocked` by an exception or that the retry strategy was exhausted. At this point it is possible to resolve 
the blocked interaction in 2 ways. This one involves resolving the interaction with a chosen `EventInstance` to replace
the one that would have had been computed by the `InteractionInstance`.

_Note: this behaviour can be automatically preconfigured by using the `FireEventAfterFailure(eventName)` `FailureStrategy`
on the `Interaction` of the `Recipe`_

=== "Scala"

    ```scala 
    val program: Future[Unit] = 
        baker.resolveInteraction(recipeInstanceId, "ReserveItems", ItemsReserved(List("item1")))
    ```

=== "Java"

    ```java 
    CompletableFuture<BoxedUnit> program = 
        baker.resolveInteraction(recipeInstanceId, "ReserveItems", new ItemsReserved(List("item1")));
    ```

## baker.stopRetryingInteraction(recipeInstanceId, interactionName)

If an `Interaction` is configured with a `RetryWithIncrementalBackoff` `FailureStrategy` then it will not stop retrying 
until you call this API or a successful outcome happens from the `InteractionInstance`.

=== "Scala"

    ```scala 
    val program: Future[Unit] = 
        baker.stopRetryingInteraction(recipeInstanceId, "ReserveItems")
    ```

=== "Java"

    ```java 
    CompletableFuture<BoxedUnit> program = 
        baker.stopRetryingInteraction(recipeInstanceId, "ReserveItems");
    ```
