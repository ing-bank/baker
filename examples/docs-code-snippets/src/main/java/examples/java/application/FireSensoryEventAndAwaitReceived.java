package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

public class FireSensoryEventAndAwaitReceived {

    private final Baker baker;

    public FireSensoryEventAndAwaitReceived(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);
        var sensoryEventStatus = baker.fireSensoryEventAndAwaitReceived(recipeInstanceId, eventInstance).join();
    }
}
