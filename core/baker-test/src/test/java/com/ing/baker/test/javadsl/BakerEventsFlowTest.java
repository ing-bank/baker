package com.ing.baker.test.javadsl;

import org.junit.Assert;
import org.junit.Test;

public class BakerEventsFlowTest {
    @Test
    public void testClassVsString() {
        Assert.assertEquals(BakerEventsFlow.of("Object"), BakerEventsFlow.ofClass(Object.class));
    }

    @Test
    public void testOrderDoesNotMatter() {
        Assert.assertEquals(BakerEventsFlow.of("a", "b", "c"), BakerEventsFlow.of("c", "a", "b"));
    }

    @Test
    public void testAddEvent() {
        BakerEventsFlow original = BakerEventsFlow.of("a", "b", "c");
        Assert.assertNotEquals(original, original.add("d"));
        Assert.assertEquals(BakerEventsFlow.of("a", "b", "c", "d"), original.add("d"));
    }

    @Test
    public void testRemoveEvent() {
        Assert.assertEquals(BakerEventsFlow.of("a"), BakerEventsFlow.of("a", "Object").removeClass(Object.class));
    }

    @Test
    public void testEmpty() {
        Assert.assertEquals(BakerEventsFlow.of(), BakerEventsFlow.of());
        Assert.assertEquals(BakerEventsFlow.of(), BakerEventsFlow.of("a").remove("a"));
    }

    @Test
    public void testMultipleBakerFlows() {
        BakerEventsFlow firstFlow = BakerEventsFlow.of("a", "b", "c");
        BakerEventsFlow secondFlow = BakerEventsFlow.of("d", "e", "f");
        Assert.assertEquals(firstFlow.add(secondFlow), BakerEventsFlow.of("a", "b", "c", "d", "e", "f"));
        Assert.assertEquals(firstFlow.add(secondFlow), secondFlow.add(firstFlow));
        Assert.assertEquals(firstFlow.remove(BakerEventsFlow.of("b", "c")), BakerEventsFlow.of("a"));
    }
}
