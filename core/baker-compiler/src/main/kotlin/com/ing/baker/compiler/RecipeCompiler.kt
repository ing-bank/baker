package com.ing.baker.compiler

import com.ing.baker.compiler.PreCompileValidations.preCompileAssertions
import com.ing.baker.compiler.ScalaConversions.asJava
import com.ing.baker.compiler.ScalaConversions.asScala
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.EventDescriptor
import com.ing.baker.il.IngredientDescriptor
import com.ing.baker.il.RecipeValidations
import com.ing.baker.il.ValidationSettings
import com.ing.baker.il.failurestrategy.`BlockInteraction$`
import com.ing.baker.il.failurestrategy.FireEventAfterFailure
import com.ing.baker.il.failurestrategy.FireFunctionalEventAfterFailure
import com.ing.baker.il.failurestrategy.RetryWithIncrementalBackoff
import com.ing.baker.il.`package$`
import com.ing.baker.il.petrinet.Edge
import com.ing.baker.il.petrinet.EventTransition
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.petrinet.IntermediateTransition
import com.ing.baker.il.petrinet.MissingEventTransition
import com.ing.baker.il.petrinet.MultiFacilitatorTransition
import com.ing.baker.il.petrinet.Place
import com.ing.baker.il.petrinet.Place.FiringLimiterPlace
import com.ing.baker.il.petrinet.Transition
import com.ing.baker.petrinet.api.PetriNet
import com.ing.baker.recipe.CheckPointEvent
import com.ing.baker.recipe.Recipe
import com.ing.baker.recipe.Sieve
import com.ing.baker.recipe.Event
import com.ing.baker.recipe.EventOutputTransformer
import com.ing.baker.recipe.Ingredient
import com.ing.baker.recipe.InteractionDescriptor
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.Recipe as ScalaRecipe
import com.ing.baker.recipe.scaladsl.Interaction
import com.ing.baker.recipe.toKotlin
import com.ing.baker.types.`NullValue$`
import com.ing.baker.types.OptionType
import com.ing.baker.types.Type
import com.ing.baker.types.Value
import scala.None
import scala.`None$`
import scala.Option
import scala.Some
import scala.collection.immutable.Seq
import scala.concurrent.duration.FiniteDuration
import scala.reflect.ClassTag
import scala.util.Either
import scala.util.Left
import scala.util.Right
import scalax.collection.Graph
import scalax.collection.`Graph$`
import scalax.collection.GraphEdge
import scalax.collection.config.CoreConfig
import scalax.collection.config.GraphConfig
import scalax.collection.edge.WLDiEdge
import scalax.collection.edge.`WLDiEdge$`
import scalax.collection.mutable.ArraySet
import kotlin.time.Duration
import com.ing.baker.il.CompiledRecipe.`Scala212CompatibleScala$`.`MODULE$` as Scala212CompatibleScala
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy as ILInteractionFailureStrategy
import com.ing.baker.il.`package$`.`MODULE$` as ILPackage
import com.ing.baker.il.petrinet.Place.`EmptyEventIngredientPlace$`.`MODULE$` as EmptyEventIngredientPlace
import com.ing.baker.il.petrinet.Place.`EventPreconditionPlace$`.`MODULE$` as EventPreconditionPlace
import com.ing.baker.il.petrinet.Place.`IngredientPlace$`.`MODULE$` as IngredientPlace
import com.ing.baker.il.petrinet.Place.`InteractionEventOutputPlace$`.`MODULE$` as InteractionEventOutputPlace
import com.ing.baker.il.petrinet.Place.`IntermediatePlace$`.`MODULE$` as IntermediatePlace
import com.ing.baker.il.petrinet.Place.`MultiTransitionPlace$`.`MODULE$` as MultiTransitionPlace

/**
 * Type alias for the node type of the scalax.collection.Graph backing the petri net.
 */
typealias Node = Either<Place, Transition>

/**
 * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
 */
typealias Arc = WLDiEdge<Node>

/**
 * Type alias for a multi set.
 */
typealias MultiSet<X> = Map<X, Int>

/**
 * Type alias for a marking.
 */
typealias Marking<X> = Map<X, MultiSet<Any?>>

/**
 * Holds all components prepared from the recipe during the preparation phase.
 */
internal data class RecipeComponents(
    val actionDescriptors: List<InteractionDescriptor>,
    val sensoryEvents: Set<Event>,
    val allIngredientNames: Set<String>
)

/**
 * Holds all transition types built during the transition building phase.
 */
internal data class TransitionCollections(
    val allInteractionTransitions: List<InteractionTransition>,
    val sensoryEventTransitions: List<EventTransition>,
    val interactionEventTransitions: List<EventTransition>,
    val allEventTransitions: List<EventTransition>,
    val multipleOutputFacilitatorTransitions: List<Transition>
)

object RecipeCompiler {

    /**
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @return
     */
    @JvmStatic
    fun compileRecipe(recipe: ScalaRecipe): CompiledRecipe =
        compileRecipe(recipe, ValidationSettings.defaultValidationSettings())

    /**
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @param validationSettings The validation settings to follow for the validation
     * @return
     */
    @JvmStatic
    fun compileRecipe(
        recipe: ScalaRecipe,
        validationSettings: ValidationSettings
    ): CompiledRecipe =
        compileRecipe(recipe.toKotlin(), validationSettings)

    /**
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @param validationSettings The validation settings to follow for the validation
     * @return
     */
    @JvmStatic
    fun compileRecipe(
        recipe: Recipe,
        validationSettings: ValidationSettings
    ): CompiledRecipe {

        val precompileErrors: List<String> = preCompileAssertions(recipe)

        val (actionDescriptors, sensoryEvents, allIngredientNames) = prepareRecipeComponents(recipe)

        val transitions = buildAllTransitions(
            actionDescriptors,
            allIngredientNames,
            sensoryEvents,
            recipe.defaultFailureStrategy
        )

        val arcs = buildAllPetriNetArcs(actionDescriptors, transitions)

        val preconditionErrors = buildPreconditionErrors(transitions, actionDescriptors)

        return assemblePetriNetAndValidate(recipe, arcs, precompileErrors, preconditionErrors, validationSettings)
    }
    /**
     * Gathers all components from the recipe including action descriptors, sensory events, and ingredient names.
     */
    internal fun prepareRecipeComponents(recipe: Recipe): RecipeComponents {
        // Extend the interactions with the checkpoint event interactions and sub-recipes
        val actionDescriptors: List<InteractionDescriptor> = recipe.interactions +
                recipe.checkpointEvents.map(::convertCheckpointEventToInteraction) +
                recipe.sieves.map(::convertSieveToInteraction) +
                recipe.subRecipes.flatMap(::flattenSubRecipesToInteraction)

        val sensoryEvents = flattenSensoryEvents(recipe)

        //All ingredient names provided by sensory events or by interactions
        val allIngredientNames: Set<String> =
            sensoryEvents
                .flatMap { e -> e.providedIngredients.map(Ingredient::name) }
                .toSet() +
                    actionDescriptors.flatMap { i ->
                        i.output.flatMap { e ->
                            // check if the event was renamed (check if there is a transformer for this event)
                            when (val transformer = i.eventOutputTransformers[e]) {
                                null -> e.providedIngredients.map(Ingredient::name)
                                else -> e.providedIngredients.map { ingredient ->
                                    transformer.ingredientRenames[ingredient.name] ?: ingredient.name
                                }
                            }
                        }
                    }

        return RecipeComponents(actionDescriptors, sensoryEvents, allIngredientNames)
    }

    /**
     * Creates interaction transitions, event transitions, and facilitator transitions.
     */
    internal fun buildAllTransitions(
        actionDescriptors: List<InteractionDescriptor>,
        allIngredientNames: Set<String>,
        sensoryEvents: Set<Event>,
        failureStrategy: InteractionFailureStrategy,
    ): TransitionCollections {
        // For inputs for which no matching output cannot be found, we do not want to generate a place.
        // It should be provided at runtime from outside the active petri net (marking)
        val allInteractionTransitions: List<InteractionTransition> =
            actionDescriptors.map { interactionTransitionOf(it, failureStrategy, allIngredientNames) }

        // events provided from outside
        val sensoryEventTransitions: List<EventTransition> = sensoryEvents.map { event ->
            EventTransition(
                EventDescriptor(
                    event.name,
                    event.providedIngredients.map { IngredientDescriptor(it.name, it.type) }.asScala
                ), true, event.maxFiringLimit.asScala
            )
        }

        // events provided by other transitions / actions
        val interactionEventTransitions: List<EventTransition> = allInteractionTransitions.flatMap { t ->
            t.eventsToFire().asJava.map { event -> EventTransition(event, false, Option.empty()) }
        }

        val allEventTransitions: List<EventTransition> = sensoryEventTransitions + interactionEventTransitions

        val multipleOutputFacilitatorTransitions: List<Transition> =
            buildMultipleOutputFacilitatorTransitions(allInteractionTransitions)

        return TransitionCollections(
            allInteractionTransitions,
            sensoryEventTransitions,
            interactionEventTransitions,
            allEventTransitions,
            multipleOutputFacilitatorTransitions
        )
    }

    /**
     * Builds internal event arcs that connect interaction transitions to ingredient places.
     */
    internal fun buildInternalEventArcs(
        allInteractionTransitions: List<InteractionTransition>,
        interactionEventTransitions: List<EventTransition>
    ): List<Arc> {
        // Given the event classes, it is creating the ingredient places and
        // connecting a transition to a ingredient place.
        val internalEventArcs: List<Arc> = allInteractionTransitions.flatMap { t ->
            t.eventsToFire.flatMap { event ->
                event.ingredients.map { ingredient ->
                    val from =
                        interactionEventTransitions.find { it.label() == event.name() }
                            ?: throw RecipeValidationException()
                    arc(from, createPlace(ingredient.name(), IngredientPlace))
                }
            }
        }
        return internalEventArcs
    }

    /**
     * Builds event limiter arcs for sensory events with firing limits.
     */
    internal fun buildEventLimiterArcs(sensoryEventTransitions: List<EventTransition>): List<Arc> {
        val eventLimiterArcs = sensoryEventTransitions.flatMap { t ->
            when (val n = t.maxFiringLimit().getOrElse { null as Int? }) {
                null -> emptyList()
                else -> listOf(arc(createPlace("limit:${t.label()}", FiringLimiterPlace(n)), t))
            }
        }

        return eventLimiterArcs
    }

    /**
     * Builds event precondition arcs (AND and OR) for all interactions.
     */
    internal fun buildEventPreconditionArcs(
        allEventTransitions: List<EventTransition>,
        allInteractionTransitions: List<InteractionTransition>,
        actionDescriptors: List<InteractionDescriptor>
    ): List<Arc> {
        fun findEventTransitionByEventName(eventName: String) =
            allEventTransitions.find { it.event().name() == eventName }

        fun findInteractionByLabel(label: String) =
            allInteractionTransitions.find { it.label() == label } ?: throw RecipeValidationException()

        // This generates precondition arcs for Required Events (AND).
        val eventPreconditionArcs = actionDescriptors.flatMap { t ->
            buildEventAndPreconditionArcs(
                t,
                ::findEventTransitionByEventName,
                ::findInteractionByLabel
            )
        }

        // This generates precondition arcs for Required Events (OR).
        val eventOrPreconditionArcs = actionDescriptors.flatMap { t ->
            buildEventORPreconditionArcs(t, ::findEventTransitionByEventName, ::findInteractionByLabel)
        }
        return eventPreconditionArcs + eventOrPreconditionArcs
    }

    /**
     * Builds sensory event arcs connecting sensory events to ingredient places or empty places.
     */
    internal fun buildSensoryEventArcs(
        sensoryEventTransitions: List<EventTransition>,
        actionDescriptors: List<InteractionDescriptor>
    ): List<Arc> {
        val (sensoryEventWithoutIngredients, sensoryEventWithIngredients) = sensoryEventTransitions.partition { it.event().ingredients.isEmpty() }

        // It connects a sensory event to an ingredient places
        val sensoryEventArcs: List<Arc> = sensoryEventWithIngredients.flatMap { et ->
            et.event().ingredients.map { ingredient ->
                arc(et, createPlace(ingredient.name(), IngredientPlace))
            }
        }

        val eventThatArePreconditions: List<String> = actionDescriptors.flatMap { actionDescriptor ->
            actionDescriptor.requiredEvents + actionDescriptor.requiredOneOfEvents.flatten()
        }

        // It connects a sensory event to a dummy ingredient so it can be modelled into the Petri net
        val sensoryEventArcsNoIngredientsArcs: List<Arc> = sensoryEventWithoutIngredients
            //Filter out events that are preconditions to interactions
            .filterNot { sensoryEvent -> eventThatArePreconditions.contains(sensoryEvent.label()) }
            .map { sensoryEvent ->
                arc(sensoryEvent, createPlace(sensoryEvent.label(), EmptyEventIngredientPlace))
            }
        return sensoryEventArcs + sensoryEventArcsNoIngredientsArcs
    }


    /**
     * Builds facilitator transitions for ingredients with multiple consumers.
     */
    internal fun buildMultipleOutputFacilitatorTransitions(allInteractionTransitions: List<InteractionTransition>): List<Transition> {
        // First find the cases where multiple transitions depend on the same ingredient place
        val ingredientsWithMultipleConsumers: Map<String, List<InteractionTransition>> =
            getIngredientsWithMultipleConsumers(allInteractionTransitions)

        // Add one new transition for each duplicate input (the newly added one in the image above)
        val multipleOutputFacilitatorTransitions: List<Transition> =
            ingredientsWithMultipleConsumers.keys.map(::MultiFacilitatorTransition)
        return multipleOutputFacilitatorTransitions
    }

    /**
     * Builds facilitator arcs for ingredients with multiple consumers.
     */
    internal fun buildMultipleOutputFacilitatorArcs(multipleOutputFacilitatorTransitions: List<Transition>): List<Arc> =
        multipleOutputFacilitatorTransitions.map { t ->
            arc(createPlace(t.label(), IngredientPlace), t)
        }

    /**
     * Builds interaction arcs for all interactions in the recipe.
     */
    internal fun buildInteractionArcs(
        allInteractionTransitions: List<InteractionTransition>,
        multipleOutputFacilitatorTransitions: List<Transition>,
        interactionEventTransitions: List<EventTransition>
    ): List<Arc> {
        val ingredientsWithMultipleConsumers = getIngredientsWithMultipleConsumers(allInteractionTransitions)

        return allInteractionTransitions.flatMap { interactionTransition ->
            buildInteractionArcs(
                multipleOutputFacilitatorTransitions,
                ingredientsWithMultipleConsumers,
                interactionEventTransitions,
                interactionTransition
            )
        }
    }

    /**
     * Consolidates all arc building logic. Arc order is preserved for backward compatibility.
     */
    internal fun buildAllPetriNetArcs(
        actionDescriptors: List<InteractionDescriptor>,
        transitions: TransitionCollections,
    ): List<Arc> {
        val (allInteractionTransitions, sensoryEventTransitions, interactionEventTransitions, allEventTransitions, multipleOutputFacilitatorTransitions) = transitions

        val interactionArcs = buildInteractionArcs(allInteractionTransitions, multipleOutputFacilitatorTransitions, interactionEventTransitions)

        val eventPreconditionArcs = buildEventPreconditionArcs(allEventTransitions, allInteractionTransitions, actionDescriptors)

        val eventLimiterArcs: List<Arc> = buildEventLimiterArcs(sensoryEventTransitions)

        val sensoryEventArcs = buildSensoryEventArcs(sensoryEventTransitions, actionDescriptors)

        val internalEventArcs: List<Arc> = buildInternalEventArcs(allInteractionTransitions, interactionEventTransitions)

        val multipleOutputFacilitatorArcs = buildMultipleOutputFacilitatorArcs(multipleOutputFacilitatorTransitions)

        val arcs = (interactionArcs +
                eventPreconditionArcs +
                eventLimiterArcs +
                sensoryEventArcs +
                internalEventArcs +
                multipleOutputFacilitatorArcs)
        return arcs
    }

    /**
     * Constructs the final Petri net from transitions, arcs, places, and initial marking.
     */
    internal fun assemblePetriNetAndValidate(
        recipe: Recipe,
        arcs: List<Arc>,
        precompileErrors: List<String>,
        preconditionErrors: List<String>,
        validationSettings: ValidationSettings
    ): CompiledRecipe {
        val petriNet = PetriNet(graph(arcs))

        val initialMarking: Marking<Place> = petriNet.places().asJava.mapNotNull { p ->
            when (val placeType = p.placeType()) {
                is FiringLimiterPlace -> p to mapOf<Any?, Int>(null to placeType.maxLimit())
                else -> null
            }
        }.toMap()

        val errors = preconditionErrors + precompileErrors

        val compiledRecipe = CompiledRecipe.build(
            recipe.name,
            petriNet,
            initialMarking.mapValues { it.value.mapValues { it.value as Any }.asScala }.asScala,
            errors.asScala,
            recipe.eventReceivePeriod.asScala,
            recipe.retentionPeriod.asScala,
            Scala212CompatibleScala,
        )

        return RecipeValidations.postCompileValidations(compiledRecipe, validationSettings)
    }

    private fun transition(transition: Transition) = Right<Place, Transition>(transition)
    private fun place(place: Place) = Left<Place, Transition>(place)

    private fun arc(t: Transition, p: Place): Arc =
        wlDiEdge(transition(t), place(p), Edge(Option.empty()))

    private fun arc(p: Place, t: Transition, eventFilter: String? = null): Arc =
        wlDiEdge(place(p), transition(t), Edge(Option.apply(eventFilter)))

    /**
     * Creates a transition for a missing event in the recipe.
     * Creates a missing event transition placeholder.
     * Used when an interaction requires an event that doesn't exist in the recipe.
     */
    internal fun missingEventTransition(eventName: String) = MissingEventTransition(eventName)

    private fun buildEventAndPreconditionErrors(
        interaction: InteractionDescriptor,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: (String) -> Transition
    ) =
        // Find the event in available events
        interaction.requiredEvents.flatMap { eventName ->
            buildEventPreconditionErrors(
                eventName,
                preconditionTransition,
                interactionTransition(interaction.name)
            )
        }

    private fun buildEventORPreconditionErrors(
        interaction: InteractionDescriptor,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: (String) -> Transition
    ) = interaction.requiredOneOfEvents.flatMapIndexed { index: Int, orGroup: Set<String> ->
        orGroup.flatMap { eventName ->
            buildEventPreconditionErrors(
                eventName,
                preconditionTransition,
                interactionTransition(interaction.name)
            )
        }
    }

    private fun buildEventPreconditionErrors(
        eventName: String,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: Transition
    ): List<String> {

        val eventTransition = preconditionTransition(eventName)

        val notProvidedError = when (eventTransition) {
            null -> listOf("Event '$eventName' for '$interactionTransition' is not provided in the recipe")
            else -> emptyList()
        }

        return notProvidedError
    }

    /**
     * Builds a list of error messages for missing required events.
     * Validates that all event preconditions (AND and OR) are satisfied.
     *
     * @param transitions All transitions in the recipe
     * @param actionDescriptors All interaction descriptors in the recipe
     * @return List of error messages for missing required events
     */
    internal fun buildPreconditionErrors(
        transitions: TransitionCollections,
        actionDescriptors: List<InteractionDescriptor>
    ): List<String> {
        fun findEventTransitionByEventName(eventName: String) =
            transitions.allEventTransitions.find { it.event().name() == eventName }

        fun findInteractionByLabel(label: String) =
            transitions.allInteractionTransitions.find { it.label() == label } ?: throw RecipeValidationException()

        // This generates precondition errors for Required Events (AND).
        val preconditionANDErrors = actionDescriptors.flatMap { t ->
            buildEventAndPreconditionErrors(t, ::findEventTransitionByEventName, ::findInteractionByLabel)
        }

        // This generates precondition errors for Required Events (OR).
        val preconditionORErrors = actionDescriptors.flatMap { t ->
            buildEventORPreconditionErrors(t, ::findEventTransitionByEventName, ::findInteractionByLabel)
        }
        return preconditionORErrors + preconditionANDErrors
    }

    private fun buildEventAndPreconditionArcs(
        interaction: InteractionDescriptor,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: (String) -> Transition
    ) =
        // Find the event in available events
        interaction.requiredEvents.flatMap { eventName ->
            // a new `Place` generated for each AND events
            val eventPreconditionPlace =
                createPlace(
                    label = "$eventName-${interaction.name}",
                    placeType = EventPreconditionPlace
                )
            buildEventPreconditionArcs(
                eventName,
                eventPreconditionPlace,
                preconditionTransition,
                interactionTransition(interaction.name)
            )
        }

    private fun buildEventORPreconditionArcs(
        interaction: InteractionDescriptor,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: (String) -> Transition
    ) = interaction.requiredOneOfEvents.flatMapIndexed { index: Int, orGroup: Set<String> ->
        // only one `Place` for all the OR events
        val eventPreconditionPlace = createPlace(
            label = "${interaction.name}-or-$index",
            placeType = EventPreconditionPlace
        )
        orGroup.flatMap { eventName ->
            buildEventPreconditionArcs(
                eventName,
                eventPreconditionPlace,
                preconditionTransition,
                interactionTransition(interaction.name)
            )
        }
    }

    private fun buildEventPreconditionArcs(
        eventName: String,
        preconditionPlace: Place,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: Transition
    ): List<Arc> {

        val eventTransition = preconditionTransition(eventName)

        val arcs = listOf(
            arc(eventTransition ?: missingEventTransition(eventName), preconditionPlace),
            arc(preconditionPlace, interactionTransition)
        )

        return arcs
    }

    // the (possible) event output arcs / places
    private fun buildInteractionOutputArcs(
        interaction: InteractionTransition,
        eventTransitions: List<EventTransition>
    ) =
        if (interaction.eventsToFire.isNotEmpty()) {
            val resultPlace =
                createPlace(label = interaction.label(), placeType = InteractionEventOutputPlace)
            val eventArcs = interaction.eventsToFire.flatMap { event: EventDescriptor ->
                //Get the correct event transition
                val eventTransition = eventTransitions.find { it.event().name() == event.name() }
                    ?: throw RecipeValidationException("eventTransition should be found")
                //Decide if there are multiple interactions that fire this transition,
                // if so create a event combiner place
                // else link the transition to the event.
                val eventTransitionCount = eventTransitions.count { e -> e.event().name() == event.name() }
                if (eventTransitionCount > 1) {
                    //Create a new intermediate event place
                    val eventCombinerPlace: Place =
                        createPlace(label = event.name(), placeType = IntermediatePlace)
                    //Create a new intermediate event transition
                    val interactionToEventTransition: IntermediateTransition =
                        IntermediateTransition("${interaction.interactionName()}:${event.name()}")
                    //link the interaction output place to the intermediate transition
                    val interactionOutputPlaceToIntermediateTransition: Arc =
                        arc(resultPlace, interactionToEventTransition, event.name())
                    //link the intermediate transition to the intermediate input place
                    val intermediateTransitionToEventCombinerPlace: Arc =
                        arc(interactionToEventTransition, eventCombinerPlace)
                    //Link the intermediate place to the event place
                    val eventCombinerPlaceToEventTransition = arc(eventCombinerPlace, eventTransition)
                    listOf(
                        intermediateTransitionToEventCombinerPlace,
                        interactionOutputPlaceToIntermediateTransition,
                        eventCombinerPlaceToEventTransition
                    )
                } else {
                    listOf(arc(resultPlace, eventTransition, event.name()))
                }
            }
            eventArcs + arc(interaction, resultPlace)
        } else emptyList()

    /**
     * Draws an arc from all required ingredients for an interaction
     * If the ingredient has multiple consumers create a multi transition place and create both arcs for it
     */
    private fun buildInteractionInputArcs(
        t: InteractionTransition,
        multipleOutputFacilitatorTransitions: List<Transition>,
        ingredientsWithMultipleConsumers: Map<String, List<InteractionTransition>>
    ): List<Arc> {

        val (fieldNamesWithPrefixMulti, fieldNamesWithoutPrefix) =
            t.nonProvidedIngredients.map(IngredientDescriptor::name)
                .partition(ingredientsWithMultipleConsumers::contains)

        // the extra arcs to model multiple output transitions from one place
        val internalDataInputArcs = fieldNamesWithPrefixMulti.flatMap { fieldName ->
            val multiTransitionPlace =
                createPlace("${t.label()}-$fieldName", placeType = MultiTransitionPlace)
            listOf(
                // one arc from multiplier place to the transition
                arc(getMultiTransition(fieldName, multipleOutputFacilitatorTransitions), multiTransitionPlace),
                // one arc from extra added place to transition
                arc(multiTransitionPlace, t)
            )
        }

        // the data input arcs / places
        val dataInputArcs: List<Arc> = fieldNamesWithoutPrefix.map { fieldName ->
            arc(createPlace(fieldName, IngredientPlace), t)
        }

        val dataOutputArcs: List<Arc> =
            if (t.isReprovider)
                fieldNamesWithoutPrefix.map { fieldName ->
                    arc(t, createPlace(fieldName, IngredientPlace))
                } + fieldNamesWithPrefixMulti.map { fieldName ->
                    arc(t, createPlace("${t.label()}-$fieldName", placeType = MultiTransitionPlace))
                }
            else
                emptyList()

        val limitInteractionCountArc: List<Arc> = when (val maximumInteractionCount = t.maximumInteractionCount) {
            null -> emptyList()
            else -> listOf(
                arc(createPlace("limit:${t.label()}", FiringLimiterPlace(maximumInteractionCount)), t)
            )
        }

        return dataInputArcs + dataOutputArcs + internalDataInputArcs + limitInteractionCountArc
    }

    private fun buildInteractionArcs(
        multipleOutputFacilitatorTransitions: List<Transition>,
        placeNameWithDuplicateTransitions: Map<String, List<InteractionTransition>>,
        eventTransitions: List<EventTransition>, interactionTransition: InteractionTransition
    ) =
        buildInteractionInputArcs(
            interactionTransition,
            multipleOutputFacilitatorTransitions,
            placeNameWithDuplicateTransitions
        ) + buildInteractionOutputArcs(
            interactionTransition,
            eventTransitions
        )

    /**
     * Finds a multi-transition (facilitator transition) by its internal representation name.
     */
    private fun getMultiTransition(internalRepresentationName: String, transitions: List<Transition>) =
        transitions.find { it.label().equals(internalRepresentationName) }
            ?: throw NoSuchElementException("No multi transition found with name $internalRepresentationName")

    /**
     * Obtains a map of each input place name that is used multiple times and the reflected transitions using it.
     *
     * @param actionTransitions Seq of reflected transition.
     * @return A map from input place name to reflected transitions (where the transitions have as input the place).
     */
    private fun getIngredientsWithMultipleConsumers(actionTransitions: List<InteractionTransition>): Map<String, List<InteractionTransition>> =
        // Obtain a list of field name with their transition
        actionTransitions
            .flatMap { transition ->
                transition.nonProvidedIngredients.map { ingredient ->
                    ingredient.name() to transition
                }
            }
            .groupBy({ it.first }, { it.second })
            // Only keep those place names which have more than one out-adjacent transition
            .filter { (_, interactions) -> interactions.size >= 2 }

    /**
     * Creates a Place with the given label and type.
     * The label is prefixed with the place type's prefix.
     * Creates a Place in the Petri net with the appropriate label prefix.
     */
    internal fun createPlace(label: String, placeType: Place.PlaceType): Place =
        Place("${placeType.labelPrepend()}$label", placeType)

    /**
     * Converts a CheckPointEvent into an InteractionDescriptor.
     * Checkpoint events are special events that can be used to track progress in a recipe.
     * They are converted to interactions with no input ingredients.
     */
    private fun convertCheckpointEventToInteraction(e: CheckPointEvent) =
        interaction(
            name = "${`package$`.`MODULE$`.checkpointEventInteractionPrefix()}${e.name}",
            inputIngredients = emptyList(),
            output = listOf(Event(e.name, emptyList())),
            requiredEvents = e.requiredEvents,
            requiredOneOfEvents = e.requiredOneOfEvents
        )

    /**
     * Converts a Sieve into an InteractionDescriptor.
     * Sieves are interactions that filter/transform ingredients without requiring specific events.
     */
    private fun convertSieveToInteraction(s: Sieve) =
        interaction(
            name = "${`package$`.`MODULE$`.sieveInteractionPrefix()}${s.name}",
            inputIngredients = s.inputIngredients,
            output = s.output,
        )

    /**
     * Flattens sub-recipes into InteractionDescriptors.
     * Each interaction in a sub-recipe is copied and prefixed to avoid name conflicts.
     */
    private fun flattenSubRecipesToInteraction(recipe: Recipe): Set<InteractionDescriptor> {
        fun copyInteraction(i: InteractionDescriptor) = com.ing.baker.recipe.Interaction(
            $$"$${ILPackage.subRecipePrefix()}$${recipe.name}$$${i.name}",
            i.originalName,
            i.inputIngredients,
            i.output,
            i.requiredEvents,
            i.requiredOneOfEvents,
            i.predefinedIngredients,
            i.overriddenIngredientNames,
            i.overriddenOutputIngredientName,
            i.eventOutputTransformers,
            i.maximumInteractionCount,
            i.failureStrategy,
            i.isReprovider,
        )
        return recipe.interactions.map(::copyInteraction).toSet() +
                recipe.checkpointEvents.map(::convertCheckpointEventToInteraction) +
                recipe.subRecipes.flatMap(::flattenSubRecipesToInteraction) +
                recipe.sieves.map(::convertSieveToInteraction)
    }

    /**
     * Flattens sensory events from a recipe including events from sub-recipes recursively.
     */
    private fun flattenSensoryEvents(recipe: Recipe): Set<Event> =
        recipe.sensoryEvents + recipe.subRecipes.flatMap(::flattenSensoryEvents)

    /**
     * Creates a Petri net graph from a list of arcs.
     * Uses the Scala graph library to construct the graph structure.
     */
    private fun graph(arcs: List<Arc>): Graph<Node, WLDiEdge<Any>> =
        `Graph$`.`MODULE$`.from(
            arcs.map { it as WLDiEdge<Any> }.asScala,
            ClassTag.apply(WLDiEdge::class.java),
            CoreConfig(GraphConfig.defaultOrder(), ArraySet.`Hints$`.`MODULE$`.apply(16, 32, 48, 80))
        ) as Graph<Node, WLDiEdge<Any>>

    /**
     * Creates a weighted labeled directed edge between two nodes.
     * Used to create arcs in the Petri net graph.
     */
    private fun <N, L> wlDiEdge(node1: Node, node2: Node, label: L): WLDiEdge<N> =
        `WLDiEdge$`.`MODULE$`.newEdge(GraphEdge.`NodeProduct$`.`MODULE$`.apply(node1, node2), 1.0, label)

    /**
     * Converts an InteractionDescriptor to an InteractionTransition for use in the Petri net.
     *
     * This function transforms recipe-level interaction descriptors into IL-level transitions,
     * handling event transformations, ingredient mapping, optional ingredients, and failure strategies.
     */
    internal fun interactionTransitionOf(
        interactionDescriptor: InteractionDescriptor,
        defaultFailureStrategy: InteractionFailureStrategy,
        allIngredientNames: Set<String>
    ): InteractionTransition {
        //This transforms the event using the eventOutputTransformer to the new event
        //If there is no eventOutputTransformer for the event the original event is returned
        fun transformEventType(event: Event): Event =
            when (val eventOutputTransformer = interactionDescriptor.eventOutputTransformers[event]) {
                null -> event
                else -> Event(
                    eventOutputTransformer.newEventName,
                    event.providedIngredients.map { i ->
                        Ingredient(
                            eventOutputTransformer.ingredientRenames.getOrElse(i.name, { i.name }),
                            i.type
                        )
                    },
                    null
                )
            }

        fun transformEventOutputTransformer(recipeEventOutputTransformer: EventOutputTransformer): com.ing.baker.il.EventOutputTransformer =
            com.ing.baker.il.EventOutputTransformer(
                recipeEventOutputTransformer.newEventName,
                recipeEventOutputTransformer.ingredientRenames.asScala
            )

        fun transformEventToCompiledEvent(event: Event): EventDescriptor =
            EventDescriptor(
                event.name,
                event.providedIngredients.map { IngredientDescriptor(it.name, it.type) }.asScala
            )

        // Replace RecipeInstanceId to recipeInstanceIdName tag as know in compiledRecipe
        // Replace BakerMetaData to BakerMetaData tag as know in compiledRecipe
        // Replace BakerEventList to BakerEventList tag as know in compiledRecipe
        // Replace ingredient tags with overridden tags
        val inputFields: Seq<Pair<String, Type>> = interactionDescriptor.inputIngredients
            .map { ingredient ->
                when (ingredient.name) {
                    com.ing.baker.recipe.common.`package$`.`MODULE$`.recipeInstanceIdName() -> ILPackage.recipeInstanceIdName()
                    com.ing.baker.recipe.common.`package$`.`MODULE$`.recipeInstanceMetadataName() -> ILPackage.recipeInstanceMetadataName()
                    com.ing.baker.recipe.common.`package$`.`MODULE$`.recipeInstanceEventListName() -> ILPackage.recipeInstanceEventListName()
                    else -> interactionDescriptor.overriddenIngredientNames
                        .getOrElse(ingredient.name, { ingredient.name })
                } to ingredient.type
            }.asScala

        val originalEvents = interactionDescriptor.output.map(::transformEventToCompiledEvent).asScala
        val eventsToFire =
            interactionDescriptor.output.map(::transformEventType).map(::transformEventToCompiledEvent).asScala

        //For each ingredient that is not provided
        //And is of the type Optional or Option
        //Add it to the predefinedIngredients List as empty
        //Add the predefinedIngredients later to overwrite any created empty field with the given predefined value.
        val predefinedIngredientsWithOptionalsEmpty: Map<String, Value> =
            inputFields.asJava
                .filter { (name, type) -> type is OptionType && name !in allIngredientNames }
                .associate { Pair(it.first, `NullValue$`.`MODULE$`) } +
                    interactionDescriptor.predefinedIngredients

        val p: Triple<ILInteractionFailureStrategy, Option<EventDescriptor>, Option<EventDescriptor>> =
            when (val strategy = interactionDescriptor.failureStrategy ?: defaultFailureStrategy) {
                is InteractionFailureStrategy.RetryWithIncrementalBackoff -> {
                    val exhaustedRetryEvent = when (val e = strategy.fireRetryExhaustedEvent()) {
                        is Some -> Some(
                            EventDescriptor(
                                e.value().getOrElse { null as String? }
                                    ?: (interactionDescriptor.name + ILPackage.exhaustedEventAppend()),
                                emptyList<IngredientDescriptor>().asScala)
                        )

                        else -> Option.empty()
                    }
                    val functionalFailedEvent = when (val e = strategy.fireFunctionalEvent()) {
                        is Some -> Some(
                            EventDescriptor(
                                e.value().getOrElse { null as String? }
                                    ?: (interactionDescriptor.name + ILPackage.functionalFailedEventAppend()),
                                emptyList<IngredientDescriptor>().asScala)
                        )

                        else -> Option.empty()
                    }
                    Triple(
                        RetryWithIncrementalBackoff(
                            strategy.initialDelay(),
                            strategy.backoffFactor(),
                            strategy.maximumRetries(),
                            strategy.maxTimeBetweenRetries(),
                            exhaustedRetryEvent,
                            functionalFailedEvent,
                        ), exhaustedRetryEvent, functionalFailedEvent
                    )
                }

                is InteractionFailureStrategy.BlockInteraction -> Triple(
                    `BlockInteraction$`.`MODULE$`,
                    Option.empty(),
                    Option.empty()
                )

                is InteractionFailureStrategy.FireEventAfterFailure -> {
                    val eventName = strategy.eventName()
                        .getOrElse { interactionDescriptor.name + ILPackage.exhaustedEventAppend() }
                    val exhaustedRetryEvent = EventDescriptor(eventName, emptyList<IngredientDescriptor>().asScala)
                    Triple(FireEventAfterFailure(exhaustedRetryEvent), Some(exhaustedRetryEvent), Option.empty())
                }

                is InteractionFailureStrategy.FireEventAndBlock -> {
                    val eventName = strategy.eventName()
                        .getOrElse { interactionDescriptor.name + ILPackage.exhaustedEventAppend() }
                    val exhaustedRetryEvent = EventDescriptor(eventName, emptyList<IngredientDescriptor>().asScala)
                    Triple(FireEventAfterFailure(exhaustedRetryEvent), Some(exhaustedRetryEvent), Option.empty())
                }

                is InteractionFailureStrategy.FireEventAndResolve -> {
                    val eventName = strategy.eventName()
                        .getOrElse { interactionDescriptor.name + ILPackage.functionalFailedEventAppend() }
                    val functionalFailed = EventDescriptor(eventName, emptyList<IngredientDescriptor>().asScala)
                    Triple(FireFunctionalEventAfterFailure(functionalFailed), Option.empty(), Some(functionalFailed))
                }

                else -> Triple(`BlockInteraction$`.`MODULE$`, Option.empty(), Option.empty())
            }
        val failureStrategy = p.first
        val exhaustedRetryEvent = p.second.toList().toSeq()
        val functionalRetryEvent = p.third.toList().toSeq()

        val eventsToFireAll = eventsToFire.asJava + exhaustedRetryEvent.asJava + functionalRetryEvent.asJava
        val originalEventsAll = originalEvents.asJava + exhaustedRetryEvent.asJava + functionalRetryEvent.asJava

        return InteractionTransition(
            eventsToFireAll.asScala,
            originalEventsAll.asScala,
            inputFields.asJava.map { (name, ingredientType) -> IngredientDescriptor(name, ingredientType) }.asScala,
            interactionDescriptor.name,
            interactionDescriptor.originalName,
            predefinedIngredientsWithOptionalsEmpty.asScala,
            interactionDescriptor.maximumInteractionCount.asScala,
            failureStrategy,
            interactionDescriptor.eventOutputTransformers.map { (event, transformer) ->
                event.name to transformEventOutputTransformer(
                    transformer
                )
            }.toMap().asScala,
            interactionDescriptor.isReprovider
        )
    }

    /**
     * Creates an Interaction descriptor with the specified configuration.
     *
     * Helper function that constructs a Scala Interaction object from Kotlin/Java types,
     * converting collections and options to their Scala equivalents.
     */
    private fun interaction(
        name: String,
        inputIngredients: List<Ingredient>,
        output: List<Event>,
        requiredEvents: Set<String> = emptySet(),
        requiredOneOfEvents: Set<Set<String>> = emptySet(),
        predefinedIngredients: Map<String, Value> = emptyMap(),
        overriddenIngredientNames: Map<String, String> = emptyMap(),
        overriddenOutputIngredientName: String? = null,
        maximumInteractionCount: Int? = null,
        failureStrategy: InteractionFailureStrategy? = null,
        eventOutputTransformers: Map<Event, EventOutputTransformer> = emptyMap(),
        isReprovider: Boolean = false,
        oldName: String? = null,
    ) =
        com.ing.baker.recipe.Interaction(
            name,
            oldName ?: name,
            inputIngredients,
            output,
            requiredEvents,
            requiredOneOfEvents,
            predefinedIngredients,
            overriddenIngredientNames,
            overriddenOutputIngredientName,
            eventOutputTransformers,
            maximumInteractionCount,
            failureStrategy,
            isReprovider
        )
}

val InteractionTransition.eventsToFire get() = this.eventsToFire().asJava
val InteractionTransition.nonProvidedIngredients get() = this.nonProvidedIngredients().asJava
val InteractionTransition.maximumInteractionCount
    get(): Int? = this.maximumInteractionCount().getOrElse { null as Int? }
val EventDescriptor.ingredients get() = this.ingredients().asJava


