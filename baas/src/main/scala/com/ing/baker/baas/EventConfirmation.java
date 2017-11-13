package com.ing.baker.baas;

public enum EventConfirmation {

    RECEIVED("received"), COMPLETED("completed");

    public final String name;

    EventConfirmation(String name) {

        this.name = name;
    }
}
