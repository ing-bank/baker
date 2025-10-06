package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

public class FireEventAndResolveOnEvent {

    private final Baker baker;

    public FireEventAndResolveOnEvent(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);
        var sensoryEventResult = baker.fireEventAndResolveOnEvent(recipeInstanceId, eventInstance, "ExpectedEvent").join();
    }
}
