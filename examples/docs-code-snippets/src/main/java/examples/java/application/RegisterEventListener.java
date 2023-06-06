package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;

import java.util.function.BiConsumer;

public class RegisterEventListener {

    private final Baker baker;

    public RegisterEventListener(Baker baker) {
        this.baker = baker;
    }

    public void example() {
        BiConsumer<String, EventInstance> handler = (String recipeInstanceId, EventInstance event) ->
                System.out.println("Recipe Instance " + recipeInstanceId + " processed event " + event.name());

        baker.registerEventListener(handler);
    }
}
