package com.ing.baker.runtime.javadsl;

public class NamedInteraction3 implements ParentInteractionWithName{
    public SimpleEvent apply(String input) {
        return new SimpleEvent("output");
    }
}
