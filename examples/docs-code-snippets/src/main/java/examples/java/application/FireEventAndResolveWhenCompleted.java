package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;
import examples.java.events.OrderPlaced;

public class FireEventAndResolveWhenCompleted {

    private final Baker baker;

    public FireEventAndResolveWhenCompleted(Baker baker) {
        this.baker = baker;
    }

    public void example(String recipeInstanceId, OrderPlaced orderPlaced) {
        var eventInstance = EventInstance.from(orderPlaced);
        var sensoryEventResult = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, eventInstance).join();
    }
}
