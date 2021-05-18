package com.ing.baker.runtime.javadsl;

public class SimpleInteraction {

    public SimpleEvent apply(String input) {
        return new SimpleEvent("output");
    }
}
