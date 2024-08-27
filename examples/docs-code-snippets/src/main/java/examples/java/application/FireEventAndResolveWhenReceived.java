package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

public class FireEventAndResolveWhenReceived {

    private final Baker baker;

    public FireEventAndResolveWhenReceived(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);
        var sensoryEventStatus = baker.fireEventAndResolveWhenReceived(recipeInstanceId, eventInstance).join();
    }
}
