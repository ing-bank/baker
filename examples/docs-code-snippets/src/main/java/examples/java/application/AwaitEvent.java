package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

import java.time.Duration;

public class AwaitEvent {

    private final Baker baker;

    public AwaitEvent(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);
        baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, eventInstance).join();
        baker.awaitEvent(recipeInstanceId, "ExpectedEvent", Duration.ofSeconds(5)).join();
    }
}
