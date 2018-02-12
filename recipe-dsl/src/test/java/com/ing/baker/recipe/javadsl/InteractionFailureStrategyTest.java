package com.ing.baker.recipe.javadsl;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import scala.None;
import scala.Some;

import java.time.Duration;

import static com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff;
import static org.junit.Assert.assertEquals;


public class InteractionFailureStrategyTest {

    public static class ExampleEvent { }

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void shouldSetupRetryWithIncrementalBackoff() {
        RetryWithIncrementalBackoff retryWithIncrementalBackoff = new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                .withInitialDelay(Duration.ofMillis(100))
                .withMaximumRetries(10)
                .build();

        assertEquals(100, retryWithIncrementalBackoff.initialDelay().toMillis());
        assertEquals(10, retryWithIncrementalBackoff.maximumRetries());

    }

    @Test
    public void shouldGiveErrorIfNoInitialDelay() {
        exception.expect(IllegalArgumentException.class);
        new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                .withMaximumRetries(10)
                .build();
    }

    @Test
    public void shouldGiveErrorIfNoDeadlineOrMaxRetries() {
        exception.expect(IllegalArgumentException.class);
        new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                .withInitialDelay(Duration.ofMillis(100))
                .build();
    }

    @Test
    public void shouldSetupFiresEventWithClass() {

        com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure eventName =
                InteractionFailureStrategy.FireEvent("Foo");
        
        assertEquals(eventName.eventName(), Some.apply("Foo"));

        com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure clazz =
                InteractionFailureStrategy.FireEvent(ExampleEvent.class);

        assertEquals(clazz.eventName(), Some.apply("ExampleEvent"));
    }
}
