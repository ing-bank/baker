package com.ing.baker.runtime.javadsl;

interface ParentInteractionWithName {
    String name = "ParentInteractionWithNameVariable";

    public SimpleEvent apply(String input);
}
