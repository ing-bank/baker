package com.ing.baker.recipe.kotlindsl;

public class ProductAgreement {
    private final String name;
    private final long id;

    public ProductAgreement(String name, long id) {
        this.name = name;
        this.id = id;
    }

    public String getName() {
        return name;
    }

    public long getId() {
        return id;
    }
}
