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
}
