package com.ing.baker.compiler

import com.ing.baker.compiler.ScalaConversions.asScala
import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.failurestrategy.`BlockInteraction$`
import com.ing.baker.il.petrinet.EventTransition
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.recipe.common.Event
import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.common.InteractionDescriptor
import com.ing.baker.types.`Int32$`
import scala.Option

/**
 * Test data builders for creating Petri net objects directly without using the Recipe DSL.
 * 
 * These builders enable true unit testing by allowing tests to create test data in isolation,
 * without dependencies on prepareRecipeComponents() or buildAllTransitions().
 * 
 * The builders reuse RecipeCompiler helper functions where possible to minimize duplication.
 */
object TestDataBuilders {
    
    /**
     * Creates a simple EventDescriptor with the specified name and ingredient names.
     * 
     * @param eventName The name of the event
     * @param ingredientNames List of ingredient names (all typed as Int32 for simplicity)
     * @return EventDescriptor suitable for testing
     */
    fun simpleEventDescriptor(
        eventName: String,
        ingredientNames: List<String> = emptyList()
    ): EventDescriptor {
        val ingredients = ingredientNames.map { name ->
            IngredientDescriptor(name, `Int32$`.`MODULE$`)
        }
        return EventDescriptor(eventName, ingredients.asScala)
    }
    
    /**
     * Creates an EventTransition for testing.
     * 
     * @param eventName Name of the event
     * @param isSensory Whether this is a sensory event (from outside) or interaction event
     * @param maxFiringLimit Optional maximum number of times this event can fire
     * @param ingredientNames Ingredients provided by this event
     * @return EventTransition ready for use in tests
     */
    fun eventTransition(
        eventName: String,
        isSensory: Boolean = true,
        maxFiringLimit: Int? = null,
        ingredientNames: List<String> = emptyList()
    ): EventTransition {
        val event = simpleEventDescriptor(eventName, ingredientNames)
        val limit: Option<Any> = maxFiringLimit?.let { Option.apply<Any>(it) } ?: Option.empty<Any>()
        return EventTransition(event, isSensory, limit)
    }
    
    /**
     * Creates a simple InteractionTransition for testing.
     * 
     * Reuses RecipeCompiler.interactionTransitionOf to ensure compatibility.
     * 
     * @param name Name of the interaction
     * @param inputIngredientNames List of required ingredient names
     * @param outputEventNames List of event names this interaction can fire
     * @return InteractionTransition ready for use in tests
     */
    fun simpleInteractionTransition(
        name: String,
        inputIngredientNames: List<String> = emptyList(),
        outputEventNames: List<String> = emptyList()
    ): InteractionTransition {
        // Create minimal ingredients
        val ingredients = inputIngredientNames.map { 
            Ingredient(it, `Int32$`.`MODULE$`) 
        }
        
        // Create minimal events
        val events = outputEventNames.map { eventName ->
            com.ing.baker.recipe.scaladsl.Event(
                eventName,
                emptyList<Ingredient>().asScala,
                Option.empty()
            )
        }
        
        // Create minimal InteractionDescriptor using Interaction.apply
        val descriptor = com.ing.baker.recipe.scaladsl.Interaction.apply(
            name,
            ingredients.asScala,
            events.asScala,
            emptySet<String>().asScala,
            emptySet<scala.collection.immutable.Set<String>>().asScala,
            emptyMap<String, com.ing.baker.types.Value>().asScala,
            emptyMap<String, String>().asScala,
            Option.empty(),
            Option.empty(),
            Option.empty(),
            emptyMap<Event, com.ing.baker.recipe.common.EventOutputTransformer>().asScala,
            false,
            Option.empty()
        )
        
        // Reuse RecipeCompiler.interactionTransitionOf
        return RecipeCompiler.interactionTransitionOf(
            descriptor,
            `BlockInteraction$`.`MODULE$` as com.ing.baker.recipe.common.InteractionFailureStrategy,
            inputIngredientNames.toSet()
        )
    }
    
    /**
     * Creates a TransitionCollections object for testing arc building functions.
     * 
     * @param interactionTransitions List of interaction transitions
     * @param sensoryEventTransitions List of sensory event transitions
     * @param interactionEventTransitions List of interaction event transitions
     * @param facilitatorTransitions List of facilitator transitions (optional)
     * @return TransitionCollections ready for use in arc building tests
     */
    internal fun transitionCollections(
        interactionTransitions: List<InteractionTransition> = emptyList(),
        sensoryEventTransitions: List<EventTransition> = emptyList(),
        interactionEventTransitions: List<EventTransition> = emptyList(),
        facilitatorTransitions: List<com.ing.baker.il.petrinet.Transition> = emptyList()
    ): TransitionCollections {
        return TransitionCollections(
            allInteractionTransitions = interactionTransitions,
            sensoryEventTransitions = sensoryEventTransitions,
            interactionEventTransitions = interactionEventTransitions,
            allEventTransitions = sensoryEventTransitions + interactionEventTransitions,
            multipleOutputFacilitatorTransitions = facilitatorTransitions
        )
    }
    
    /**
     * Creates a minimal InteractionDescriptor for testing precondition validation.
     * 
     * @param name Name of the interaction
     * @param requiredEvents Set of event names that must occur before this interaction (AND)
     * @param requiredOneOfEvents Set of sets of event names where at least one from each set must occur (OR)
     * @return InteractionDescriptor ready for validation tests
     */
    fun interactionDescriptorWithPreconditions(
        name: String,
        requiredEvents: Set<String> = emptySet(),
        requiredOneOfEvents: Set<Set<String>> = emptySet()
    ): InteractionDescriptor {
        val scalaRequiredOneOfEvents = requiredOneOfEvents.map { it.asScala }.toSet().asScala
        
        return com.ing.baker.recipe.scaladsl.Interaction.apply(
            name,
            emptyList<Ingredient>().asScala,
            emptyList<Event>().asScala,
            requiredEvents.asScala,
            scalaRequiredOneOfEvents,
            emptyMap<String, com.ing.baker.types.Value>().asScala,
            emptyMap<String, String>().asScala,
            Option.empty(),
            Option.empty(),
            Option.empty(),
            emptyMap<Event, com.ing.baker.recipe.common.EventOutputTransformer>().asScala,
            false,
            Option.empty()
        )
    }
}
