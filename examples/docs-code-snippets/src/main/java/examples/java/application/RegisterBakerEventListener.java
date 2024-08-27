package examples.java.application;

import com.ing.baker.runtime.javadsl.Baker;
import com.ing.baker.runtime.javadsl.BakerEvent;

public class RegisterBakerEventListener {

    private final Baker baker;

    public RegisterBakerEventListener(Baker baker) {
        this.baker = baker;
    }

    public void example() {
        baker.registerBakerEventListener((BakerEvent event) ->
            System.out.println("Received event: " + event)
        );
    }
}
