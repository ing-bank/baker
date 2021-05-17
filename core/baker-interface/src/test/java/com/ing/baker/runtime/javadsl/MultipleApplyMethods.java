package com.ing.baker.runtime.javadsl;

public class MultipleApplyMethods {

    public SimpleEvent apply() {
        return new SimpleEvent("output");
    }

    public SimpleEvent apply(String output) {
        return new SimpleEvent(output);
    }
}
