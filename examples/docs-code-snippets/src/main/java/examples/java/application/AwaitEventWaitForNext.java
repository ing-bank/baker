package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

import java.time.Duration;

public class AwaitEventWaitForNext {

    private final Baker baker;

    public AwaitEventWaitForNext(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);

        // Pattern: Start waiting BEFORE firing the sensory event
        // waitForNext = true checks for *new* occurrences of the event
        var awaitFuture = baker.awaitEvent(recipeInstanceId, "ExpectedEvent", Duration.ofSeconds(5), true);
        
        // Fire the event
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, eventInstance).join();
        
        // Now wait for the event to occur
        // Because we started listening *before* firing, we are guaranteed not to miss it
        awaitFuture.join(); 
    }
}
