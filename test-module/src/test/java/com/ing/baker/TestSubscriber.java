package com.ing.baker;

import com.ing.baker.runtime.core.events.ProcessCreated;
import com.ing.baker.runtime.core.events.Subscribe;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TestSubscriber {

    private Logger log = LoggerFactory.getLogger(TestSubscriber.class);

    @Subscribe
    public void receive(ProcessCreated event) {
        log.debug("Received {} event", event);
    }
}
