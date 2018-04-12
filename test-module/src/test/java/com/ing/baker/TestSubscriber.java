package com.ing.baker;

import com.ing.baker.runtime.core.events.ProcessCreated;
import com.ing.baker.runtime.core.events.Subscribe;

public class TestSubscriber {

    @Subscribe
    public void receive(ProcessCreated event) {
        System.out.println(event.toString());
    }
}
