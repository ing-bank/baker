package com.ing.baker.compiler

import com.ing.baker.compiler.ScalaConversions.asScala
import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.petrinet.EventTransition
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.recipe.Interaction
import com.ing.baker.recipe.Event
import com.ing.baker.recipe.Ingredient
import com.ing.baker.recipe.InteractionDescriptor
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.types.`Int32$`
import com.ing.baker.types.Value
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
     * @param outputEventIngredients Map from event name to list of ingredient names for that event
     * @return InteractionTransition ready for use in tests
     */
    fun simpleInteractionTransition(
        name: String,
        inputIngredientNames: List<String> = emptyList(),
        outputEventNames: List<String> = emptyList(),
        outputEventIngredients: Map<String, List<String>> = emptyMap()
    ): InteractionTransition {
        // Create minimal ingredients
        val ingredients = inputIngredientNames.map { 
            Ingredient(it, `Int32$`.`MODULE$`) 
        }
        
        // Create minimal events with optional ingredients
        val events = outputEventNames.map { eventName ->
            val eventIngredients = outputEventIngredients[eventName] ?: emptyList()
            val ingredientList = eventIngredients.map { Ingredient(it, `Int32$`.`MODULE$`) }
            Event(
                eventName,
                ingredientList,
                null
            )
        }
        
        // Create minimal InteractionDescriptor using Interaction.apply
        val descriptor = Interaction(
            name,
            null,
            ingredients,
            events,
            emptySet<String>(),
            emptySet<Set<String>>(),
            emptyMap<String, com.ing.baker.types.Value>(),
            emptyMap<String, String>(),
            null,
            emptyMap(),
            null,
            null,
            false,
        )
        
        // Reuse RecipeCompiler.interactionTransitionOf
        return RecipeCompiler.interactionTransitionOf(
            descriptor,
            InteractionFailureStrategy.BlockInteraction(),
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
        return Interaction(
            name,
            null,
            emptyList<Ingredient>(),
            emptyList<Event>(),
            requiredEvents,
            requiredOneOfEvents,
            emptyMap<String, Value>(),
            emptyMap<String, String>(),
            null,
            emptyMap(),
            null,
            null,
            false
        )
    }
}
