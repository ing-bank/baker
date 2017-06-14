package com.ing.baker.recipe.javadsl;

import scala.collection.JavaConversions;
import scala.collection.Seq;
import scala.collection.immutable.Set;
import scala.reflect.ClassTag;

import java.util.ArrayList;
import java.util.UUID;

public class JavadslTestHelper {
    public static ClassTag<String> stringClassTag = scala.reflect.ClassTag$.MODULE$.apply(String.class);
    public static ClassTag<String> UUIDClassTag = scala.reflect.ClassTag$.MODULE$.apply(UUID.class);

    //Ingredients
    public static com.ing.baker.recipe.common.Ingredient initialIngredientCheck =
            new com.ing.baker.recipe.scaladsl.Ingredient<String>("initialIngredient", stringClassTag);
    public static com.ing.baker.recipe.common.Ingredient firstProvidedIngredientCheck =
            new com.ing.baker.recipe.scaladsl.Ingredient<String>("firstProvidedIngredient", stringClassTag);

    //Events
    public static com.ing.baker.recipe.common.Event interactionProvidedEventCheck =
            new com.ing.baker.recipe.scaladsl.Event("InteractionProvidedEvent",
                    JavaConversions.asScalaBuffer(new ArrayList<com.ing.baker.recipe.common.Ingredient>()).toSeq());

    public static com.ing.baker.recipe.common.Event interactionProvidedEvent2Check =
            new com.ing.baker.recipe.scaladsl.Event("InteractionProvidedEvent2",
                    JavaConversions.asScalaBuffer(new ArrayList<com.ing.baker.recipe.common.Ingredient>()).toSeq());

    public static com.ing.baker.recipe.common.Event initialSensoryEventCheck =
            new com.ing.baker.recipe.scaladsl.Event("InitialSensoryEvent",
                    new Set.Set1<com.ing.baker.recipe.common.Ingredient>(initialIngredientCheck).toSeq());


    //Interactions
    public static com.ing.baker.recipe.common.Ingredient ProcessIdStringCheck =
            new com.ing.baker.recipe.scaladsl.Ingredient<String>("$ProcessId$", stringClassTag);

    public static com.ing.baker.recipe.common.Ingredient ProcessIdUUIDCheck =
            new com.ing.baker.recipe.scaladsl.Ingredient<String>("$ProcessId$", UUIDClassTag);

    public static com.ing.baker.recipe.common.Interaction providesIngredientInteraction =
            new com.ing.baker.recipe.scaladsl.Interaction(
                    "ProvidesIngredientInteraction",
                    new Set.Set1<com.ing.baker.recipe.common.Ingredient>(initialIngredientCheck).toSeq(),
                    new com.ing.baker.recipe.common.ProvidesIngredient(firstProvidedIngredientCheck)
            );

    public static com.ing.baker.recipe.common.Interaction requiresProcessIdStringInteraction =
            new com.ing.baker.recipe.scaladsl.Interaction(
                    "RequiresProcessIdStringInteraction",
                    new Set.Set2<com.ing.baker.recipe.common.Ingredient>(ProcessIdStringCheck, initialIngredientCheck).toSeq(),
                    new com.ing.baker.recipe.common.ProvidesNothing()
            );

    public static com.ing.baker.recipe.common.Interaction requiresProcessIdUUIDInteraction =
            new com.ing.baker.recipe.scaladsl.Interaction(
                    "RequiresProcessIdUUIDInteraction",
                    new Set.Set2<com.ing.baker.recipe.common.Ingredient>(ProcessIdUUIDCheck, initialIngredientCheck).toSeq(),
                    new com.ing.baker.recipe.common.ProvidesNothing()
            );

    public static com.ing.baker.recipe.common.Interaction firesEventInteractionCheck =
            new com.ing.baker.recipe.scaladsl.Interaction(
                    "FiresEventInteraction",
                    (Seq<com.ing.baker.recipe.common.Ingredient>)new Set.Set1<com.ing.baker.recipe.common.Ingredient>(initialIngredientCheck).toSeq(),
                    new com.ing.baker.recipe.common.FiresOneOfEvents(
                            new Set.Set1<com.ing.baker.recipe.common.Event>(interactionProvidedEventCheck).toSeq())
            );

    public static com.ing.baker.recipe.common.Interaction firesTwoEventInteractionCheck =
            new com.ing.baker.recipe.scaladsl.Interaction(
                    "FiresTwoEventInteraction",
                    (Seq<com.ing.baker.recipe.common.Ingredient>)new Set.Set1<com.ing.baker.recipe.common.Ingredient>(initialIngredientCheck).toSeq(),
                    new com.ing.baker.recipe.common.FiresOneOfEvents(
                            new Set.Set2<com.ing.baker.recipe.common.Event>(interactionProvidedEventCheck, interactionProvidedEvent2Check).toSeq())
            );
}
