package com.ing.baker.runtime.javadsl;

public class NamedInteraction2 implements ParentInteractionWithoutName{
    public SimpleEvent apply(String input) {
        return new SimpleEvent("output");
    }
}
