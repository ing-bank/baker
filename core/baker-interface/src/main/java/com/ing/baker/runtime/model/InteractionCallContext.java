package com.ing.baker.runtime.model;

import java.util.Optional;

/**
 * Identifies a single interaction invocation, handed to {@link InteractionInstrumentation} on the thread
 * that actually invokes the interaction implementation.
 */
public final class InteractionCallContext {

    private final String recipeId;
    private final String recipeName;
    private final String recipeInstanceId;
    private final String interactionName;
    private final long executionId;
    private final String correlationId;

    public InteractionCallContext(String recipeId,
                                  String recipeName,
                                  String recipeInstanceId,
                                  String interactionName,
                                  long executionId,
                                  String correlationId) {
        this.recipeId = recipeId;
        this.recipeName = recipeName;
        this.recipeInstanceId = recipeInstanceId;
        this.interactionName = interactionName;
        this.executionId = executionId;
        this.correlationId = correlationId;
    }

    public String getRecipeId() {
        return recipeId;
    }

    public String getRecipeName() {
        return recipeName;
    }

    public String getRecipeInstanceId() {
        return recipeInstanceId;
    }

    public String getInteractionName() {
        return interactionName;
    }

    public long getExecutionId() {
        return executionId;
    }

    public Optional<String> getCorrelationId() {
        return Optional.ofNullable(correlationId);
    }

    @Override
    public String toString() {
        return "InteractionCallContext{" +
                "recipeName='" + recipeName + '\'' +
                ", recipeInstanceId='" + recipeInstanceId + '\'' +
                ", interactionName='" + interactionName + '\'' +
                ", executionId=" + executionId +
                '}';
    }
}
