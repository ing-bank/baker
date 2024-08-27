package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

public class FireEvent {

    private final Baker baker;

    public FireEvent(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);

        var eventResolutions = baker.fireEvent(recipeInstanceId, eventInstance);
        var sensoryEventStatus = eventResolutions.getResolveWhenReceived().join();
        var sensoryEventResult = eventResolutions.getResolveWhenCompleted().join();
    }
}
