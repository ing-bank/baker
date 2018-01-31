package com.ing.baker.recipe.javadsl;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.time.Duration;

import static com.ing.baker.recipe.common.InteractionFailureStrategy.*;
import static org.junit.Assert.assertEquals;


public class InteractionFailureStrategyTest {

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
        RetryWithIncrementalBackoff retryWithIncrementalBackoff = new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                .withMaximumRetries(10)
                .build();
    }

    @Test
    public void shouldGiveErrorIfNoDeadlineOrMaxRetries() {
        exception.expect(IllegalArgumentException.class);
        RetryWithIncrementalBackoff retryWithIncrementalBackoff = new InteractionFailureStrategy.RetryWithIncrementalBackoffBuilder()
                .withInitialDelay(Duration.ofMillis(100))
                .build();
    }
}
