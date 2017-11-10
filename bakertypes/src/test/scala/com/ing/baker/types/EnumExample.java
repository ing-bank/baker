package com.ing.baker.types;


public enum EnumExample {
    A("ValueA"),
    B("ValueB"),
    C("ValueC");

    public final String value;

    EnumExample(String value) {
        this.value = value;
    }
}
