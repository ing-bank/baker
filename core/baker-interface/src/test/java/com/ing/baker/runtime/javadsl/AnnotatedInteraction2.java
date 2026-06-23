package com.ing.baker.runtime.javadsl;

public class AnnotatedInteraction2 implements AnnotatedParentInteraction {

    public SimpleEvent apply(String input) {
        return new SimpleEvent("output");
    }
}
