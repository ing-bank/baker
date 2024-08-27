package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.EventInstance;

public class RegisterEventListener {

    private final Baker baker;

    public RegisterEventListener(Baker baker) {
        this.baker = baker;
    }

    public void example() {
        baker.registerEventListener((String recipeInstanceId, String event) ->
            System.out.println("Recipe Instance " + recipeInstanceId + " processed event " + event)
        );
    }
}
