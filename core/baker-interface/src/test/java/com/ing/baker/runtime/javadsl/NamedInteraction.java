package com.ing.baker.runtime.javadsl;

public class NamedInteraction {

    private String name = "InteractionNameVariable";

    public SimpleEvent apply(String input) {
        return new SimpleEvent("output");
    }
}
