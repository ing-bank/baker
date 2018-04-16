package com.ing.baker.runtime.java_api;

import com.ing.baker.runtime.core.events.*;
import org.junit.Assert;
import org.junit.Test;

import static org.mockito.Mockito.*;

public class JEventSubscriberTest {
    @Test
    public void shouldReceiveBakerEvents() {
        TestBakerEventListener listenerMock = mock(TestBakerEventListener.class);
        JEventSubscriber subscriber = new JEventSubscriber(listenerMock);

        ProcessCreated processCreated = mock(ProcessCreated.class);
        EventReceived eventReceived = mock(EventReceived.class);
        EventRejected eventRejected = mock(EventRejected.class);
        InteractionCompleted interactionCompleted = mock(InteractionCompleted.class);
        InteractionFailed interactionFailed = mock(InteractionFailed.class);
        InteractionStarted interactionStarted = mock(InteractionStarted.class);

        subscriber.apply(processCreated);
        subscriber.apply(eventReceived);
        subscriber.apply(eventRejected);
        subscriber.apply(interactionCompleted);
        subscriber.apply(interactionFailed);
        subscriber.apply(interactionStarted);

        // get notified of specific events
        verify(listenerMock).createProcess(processCreated);
        verify(listenerMock).receiveEvent(eventReceived);
        verify(listenerMock).rejectEvent(eventRejected);
        verify(listenerMock).completeInteraction(interactionCompleted);
        verify(listenerMock).failInteraction(interactionFailed);
        verify(listenerMock).startInteraction(interactionStarted);

        // get notified of all events
        verify(listenerMock).receiveBakerEvent(processCreated);
        verify(listenerMock).receiveBakerEvent(eventReceived);
        verify(listenerMock).receiveBakerEvent(eventRejected);
        verify(listenerMock).receiveBakerEvent(interactionCompleted);
        verify(listenerMock).receiveBakerEvent(interactionFailed);
        verify(listenerMock).receiveBakerEvent(interactionStarted);

        verifyNoMoreInteractions(listenerMock);
    }

    @Test
    public void failForNonBakerEventTypes() {
        NotBakerEventBakerEventListener listenerMock = mock(NotBakerEventBakerEventListener.class);
        try {
            new JEventSubscriber(listenerMock); // fail during construction
            Assert.fail();
        } catch(IllegalArgumentException e) {
            if (!e.getMessage().equals("BakerEventListener methods cannot listen other types than BakerEvent")) Assert.fail();
        } catch (Exception e) {
            Assert.fail();
        }
    }

    @Test
    public void failForInvalidListenerFunctionsWithManyParameters() {
        MoreThanOneArgumentBakerEventListener listenerMock = mock(MoreThanOneArgumentBakerEventListener.class);
        try {
            new JEventSubscriber(listenerMock); // fail during construction
            Assert.fail();
        } catch(IllegalArgumentException e) {
            if (!e.getMessage().equals("BakerEventListener methods should have only one parameter")) Assert.fail();
        } catch (Exception e) {
            Assert.fail();
        }
    }

    public interface NotBakerEventBakerEventListener {
        @Subscribe
        void onSomeEventHappened(Object someEvent);
    }

    public interface MoreThanOneArgumentBakerEventListener {
        @Subscribe
        void onEvent(ProcessCreated event1, EventReceived event2);
    }

}