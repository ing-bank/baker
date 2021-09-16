package com.ing.baker.test.javadsl;

import com.ing.baker.test.EventsFlow;
import org.junit.Assert;
import org.junit.Test;

public class EventsFlowTest {
    @Test
    public void testClassVsString() {
        Assert.assertEquals(EventsFlow.of("Object"), EventsFlow.ofClasses(Object.class));
    }

    @Test
    public void testOrderDoesNotMatter() {
        Assert.assertEquals(EventsFlow.of("a", "b", "c"), EventsFlow.of("c", "a", "b"));
    }

    @Test
    public void testAddEvent() {
        EventsFlow original = EventsFlow.of("a", "b", "c");
        Assert.assertNotEquals(original, original.add("d"));
        Assert.assertEquals(EventsFlow.of("a", "b", "c", "d"), original.add("d"));
    }

    @Test
    public void testRemoveEvent() {
        Assert.assertEquals(EventsFlow.of("a"), EventsFlow.of("a", "Object").remove(Object.class));
    }

    @Test
    public void testEmpty() {
        Assert.assertEquals(EventsFlow.of(), EventsFlow.of());
        Assert.assertEquals(EventsFlow.of(), EventsFlow.of("a").remove("a"));
    }

    @Test
    public void testMultipleBakerFlows() {
        EventsFlow firstFlow = EventsFlow.of("a", "b", "c");
        EventsFlow secondFlow = EventsFlow.of("d", "e", "f");
        Assert.assertEquals(firstFlow.add(secondFlow), EventsFlow.of("a", "b", "c", "d", "e", "f"));
        Assert.assertEquals(firstFlow.add(secondFlow), secondFlow.add(firstFlow));
        Assert.assertEquals(firstFlow.remove(EventsFlow.of("b", "c")), EventsFlow.of("a"));
    }
}
