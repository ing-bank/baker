package com.ing.baker.compiler

import com.ing.baker.compiler.PreCompileValidations.preCompileAssertions
import com.ing.baker.compiler.ScalaConversions.asJava
import com.ing.baker.compiler.ScalaConversions.asScala
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.CompiledRecipe.OldRecipeIdVariant
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
import com.ing.baker.recipe.common.CheckPointEvent
import com.ing.baker.recipe.common.Event
import com.ing.baker.recipe.common.EventOutputTransformer
import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.common.InteractionDescriptor
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.Recipe
import com.ing.baker.recipe.common.Sieve
import com.ing.baker.recipe.scaladsl.`Event$`
import com.ing.baker.recipe.scaladsl.Interaction
import com.ing.baker.types.`NullValue$`
import com.ing.baker.types.OptionType
import com.ing.baker.types.Type
import com.ing.baker.types.Value
import scala.Option
import scala.Some
import scala.collection.immutable.Seq
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
import com.ing.baker.il.CompiledRecipe.`Scala212CompatibleJava$`.`MODULE$` as Scala212CompatibleJava
import com.ing.baker.il.CompiledRecipe.`Scala212CompatibleKotlin$`.`MODULE$` as Scala212CompatibleKotlin
import com.ing.baker.il.CompiledRecipe.`Scala212CompatibleScala$`.`MODULE$` as Scala212CompatibleScala
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy as ILInteractionFailureStrategy
import com.ing.baker.il.`package$`.`MODULE$` as ILPackage
import com.ing.baker.il.petrinet.Place.`EmptyEventIngredientPlace$`.`MODULE$` as EmptyEventIngredientPlace
import com.ing.baker.il.petrinet.Place.`EventPreconditionPlace$`.`MODULE$` as EventPreconditionPlace
import com.ing.baker.il.petrinet.Place.`IngredientPlace$`.`MODULE$` as IngredientPlace
import com.ing.baker.il.petrinet.Place.`InteractionEventOutputPlace$`.`MODULE$` as InteractionEventOutputPlace
import com.ing.baker.il.petrinet.Place.`IntermediatePlace$`.`MODULE$` as IntermediatePlace
import com.ing.baker.il.petrinet.Place.`MultiTransitionPlace$`.`MODULE$` as MultiTransitionPlace
import com.ing.baker.recipe.javadsl.Recipe as JavaRecipe
import com.ing.baker.recipe.kotlindsl.Recipe as KotlinRecipe
import com.ing.baker.recipe.scaladsl.Recipe as ScalaRecipe

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


object RecipeCompilerKotlin {
    fun <A, B> List<Pair<List<A>, List<B>>>.unzipFlatten() = this.unzip().let { pair ->
        pair.first.flatten() to pair.second.flatten()
    }

    fun transition(transition: Transition) = Right<Place, Transition>(transition)
    fun place(place: Place) = Left<Place, Transition>(place)

    fun arc(t: Transition, p: Place, weight: Long): Arc =
        wlDiEdge(transition(t), place(p), weight.toDouble(), Edge(Option.empty()))

    fun arc(p: Place, t: Transition, weight: Long, eventFilter: String? = null): Arc =
        wlDiEdge(place(p), transition(t), weight.toDouble(), Edge(Option.apply(eventFilter)))

    /**
     * Creates a transition for a missing event in the recipe.
     */
    private fun missingEventTransition(eventName: String) = MissingEventTransition(eventName)

    private fun buildEventAndPreconditionArcs(
        interaction: InteractionDescriptor,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: (String) -> Transition
    ) =
        // Find the event in available events
        interaction.requiredEvents.map { eventName ->
            // a new `Place` generated for each AND events
            val eventPreconditionPlace =
                createPlace(
                    label = "$eventName-${interaction.name()}",
                    placeType = EventPreconditionPlace
                )
            buildEventPreconditionArcs(
                eventName,
                eventPreconditionPlace,
                preconditionTransition,
                interactionTransition(interaction.name())
            )
        }.unzipFlatten()

    private fun buildEventORPreconditionArcs(
        interaction: InteractionDescriptor,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: (String) -> Transition
    ) = interaction.requiredOneOfEvents.mapIndexed { index: Int, orGroup: Set<String> ->
        // only one `Place` for all the OR events
        val eventPreconditionPlace = createPlace(
            label = "${interaction.name()}-or-$index",
            placeType = EventPreconditionPlace
        )
        orGroup.map { eventName ->
            buildEventPreconditionArcs(
                eventName,
                eventPreconditionPlace,
                preconditionTransition,
                interactionTransition(interaction.name())
            )
        }.unzipFlatten()
    }.unzipFlatten()

    private fun buildEventPreconditionArcs(
        eventName: String,
        preconditionPlace: Place,
        preconditionTransition: (String) -> Transition?,
        interactionTransition: Transition
    ): Pair<List<Arc>, List<String>> {

        val eventTransition = preconditionTransition(eventName)

        val notProvidedError = when (eventTransition) {
            null -> listOf("Event '$eventName' for '$interactionTransition' is not provided in the recipe")
            else -> emptyList()
        }

        val arcs = listOf(
            arc(eventTransition ?: missingEventTransition(eventName), preconditionPlace, 1),
            arc(preconditionPlace, interactionTransition, 1)
        )

        return arcs to notProvidedError
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
                        arc(resultPlace, interactionToEventTransition, 1, event.name())
                    //link the intermediate transition to the intermediate input place
                    val intermediateTransitionToEventCombinerPlace: Arc =
                        arc(interactionToEventTransition, eventCombinerPlace, 1)
                    //Link the intermediate place to the event place
                    val eventCombinerPlaceToEventTransition = arc(eventCombinerPlace, eventTransition, 1)
                    listOf(
                        intermediateTransitionToEventCombinerPlace,
                        interactionOutputPlaceToIntermediateTransition,
                        eventCombinerPlaceToEventTransition
                    )
                } else {
                    listOf(arc(resultPlace, eventTransition, 1, event.name()))
                }
            }
            eventArcs + arc(interaction, resultPlace, 1)
        } else emptyList()

    /**
     * Draws an arc from all required ingredients for an interaction
     * If the ingredient has multiple consumers create a multi transition place and create both arcs for it
     */
    private fun buildInteractionInputArcs(
        t: InteractionTransition,
        multipleConsumerFacilitatorTransitions: List<Transition>,
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
                arc(getMultiTransition(fieldName, multipleConsumerFacilitatorTransitions), multiTransitionPlace, 1),
                // one arc from extra added place to transition
                arc(multiTransitionPlace, t, 1)
            )
        }

        // the data input arcs / places
        val dataInputArcs: List<Arc> = fieldNamesWithoutPrefix.map { fieldName ->
            arc(createPlace(fieldName, IngredientPlace), t, 1)
        }

        val dataOutputArcs: List<Arc> =
            if (t.isReprovider)
                fieldNamesWithoutPrefix.map { fieldName ->
                    arc(t, createPlace(fieldName, IngredientPlace), 1)
                } + fieldNamesWithPrefixMulti.map { fieldName ->
                    arc(t, createPlace("${t.label()}-$fieldName", placeType = MultiTransitionPlace), 1)
                }
            else
                emptyList()

        val limitInteractionCountArc: List<Arc> = when (val maximumInteractionCount = t.maximumInteractionCount) {
            null -> emptyList()
            else -> listOf(
                arc(createPlace("limit:${t.label()}", FiringLimiterPlace(maximumInteractionCount)), t, 1)
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
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @param validationSettings The validation settings to follow for the validation
     * @return
     */
    fun compileRecipe(
        recipe: Recipe,
        validationSettings: ValidationSettings
    ): CompiledRecipe {

        val precompileErrors: List<String> = preCompileAssertions(recipe).asJava

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
                                    transformer.ingredientRenames[ingredient.name()] ?: ingredient.name()
                                }
                            }
                        }
                    }

        // For inputs for which no matching output cannot be found, we do not want to generate a place.
        // It should be provided at runtime from outside the active petri net (marking)
        val allInteractionTransitions: List<InteractionTransition> =
            actionDescriptors.map { interactionTransitionOf(it, recipe.defaultFailureStrategy(), allIngredientNames) }

        // events provided from outside
        val sensoryEventTransitions: List<EventTransition> = sensoryEvents.map { event ->
            EventTransition(eventToCompiledEvent(event), true, event.maxFiringLimit())
        }

        // events provided by other transitions / actions
        val interactionEventTransitions: List<EventTransition> = allInteractionTransitions.flatMap { t ->
            t.eventsToFire.map { event -> EventTransition(event, false, Option.empty()) }
        }

        val allEventTransitions: List<EventTransition> = sensoryEventTransitions + interactionEventTransitions

        // Given the event classes, it is creating the ingredient places and
        // connecting a transition to a ingredient place.
        val internalEventArcs: List<Arc> = allInteractionTransitions.flatMap { t ->
            t.eventsToFire.flatMap { event ->
                event.ingredients.map { ingredient ->
                    val from =
                        interactionEventTransitions.find { it.label() == event.name() }
                            ?: throw RecipeValidationException()
                    arc(from, createPlace(ingredient.name(), IngredientPlace), 1)
                }
            }
        }

        //Create event limiter places so that events can only fire x amount of times.
        val eventLimiterArcs: List<Arc> = sensoryEventTransitions.flatMap { t ->
            when (val n = t.maxFiringLimit().getOrElse { null as Int? }) {
                null -> emptyList()
                else -> listOf(arc(createPlace("limit:${t.label()}", FiringLimiterPlace(n)), t, 1))
            }
        }

        fun findEventTransitionByEventName(eventName: String) =
            allEventTransitions.find { it.event().name() == eventName }

        fun findInteractionByLabel(label: String) =
            allInteractionTransitions.find { it.label() == label } ?: throw RecipeValidationException()

        // This generates precondition arcs for Required Events (AND).
        val (eventPreconditionArcs, preconditionANDErrors) = actionDescriptors.map { t ->
            buildEventAndPreconditionArcs(
                t,
                ::findEventTransitionByEventName,
                ::findInteractionByLabel
            )
        }.unzipFlatten()

        // This generates precondition arcs for Required Events (OR).
        val (eventOrPreconditionArcs, preconditionORErrors) = actionDescriptors.map { t ->
            buildEventORPreconditionArcs(t, ::findEventTransitionByEventName, ::findInteractionByLabel)
        }.unzipFlatten()

        val (sensoryEventWithoutIngredients, sensoryEventWithIngredients) = sensoryEventTransitions.partition { it.event().ingredients.isEmpty() }

        // It connects a sensory event to an ingredient places
        val sensoryEventArcs: List<Arc> = sensoryEventWithIngredients.flatMap { et ->
            et.event().ingredients.map { ingredient ->
                arc(et, createPlace(ingredient.name(), IngredientPlace), 1)
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
                arc(sensoryEvent, createPlace(sensoryEvent.label(), EmptyEventIngredientPlace), 1)
            }

        // First find the cases where multiple transitions depend on the same ingredient place
        val ingredientsWithMultipleConsumers: Map<String, List<InteractionTransition>> =
            getIngredientsWithMultipleConsumers(allInteractionTransitions)

        // Add one new transition for each duplicate input (the newly added one in the image above)
        val multipleConsumerFacilitatorTransitions: List<Transition> =
            ingredientsWithMultipleConsumers.keys.map(::MultiFacilitatorTransition)

        val multipleOutputFacilitatorArcs: List<Arc> =
            multipleConsumerFacilitatorTransitions.map { t ->
                arc(createPlace(t.label(), IngredientPlace), t, 1)
            }

        val interactionArcs: List<Arc> =
            allInteractionTransitions.flatMap { interactionTransition ->
                buildInteractionArcs(
                    multipleConsumerFacilitatorTransitions,
                    ingredientsWithMultipleConsumers,
                    interactionEventTransitions,
                    interactionTransition
                )
            }

        val arcs = (interactionArcs +
                eventPreconditionArcs +
                eventOrPreconditionArcs +
                eventLimiterArcs +
                sensoryEventArcs +
                sensoryEventArcsNoIngredientsArcs +
                internalEventArcs +
                multipleOutputFacilitatorArcs)

        val petriNet = PetriNet(graph(arcs))

        val initialMarking: Marking<Place> = petriNet.places().asJava.mapNotNull { p ->
            when (val placeType = p.placeType()) {
                is FiringLimiterPlace -> p to mapOf<Any?, Int>(null to placeType.maxLimit())
                else -> null
            }
        }.toMap()

        val errors = preconditionORErrors + preconditionANDErrors + precompileErrors

        val oldRecipeIdVariant: OldRecipeIdVariant =
            when (recipe) {
                is JavaRecipe -> Scala212CompatibleJava
                is KotlinRecipe -> Scala212CompatibleKotlin
                is ScalaRecipe -> Scala212CompatibleScala
                else -> throw RecipeValidationException("Only recipe of type java, kotlin or scala supported")
            }

        val compiledRecipe = CompiledRecipe.build(
            recipe.name(),
            petriNet,
            initialMarking.mapValues { it.value.mapValues { it.value as Any }.asScala }.asScala,
            errors.asScala,
            recipe.eventReceivePeriod(),
            recipe.retentionPeriod(),
            oldRecipeIdVariant,
        )

        return RecipeValidations.postCompileValidations(compiledRecipe, validationSettings)
    }

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

    private fun createPlace(label: String, placeType: Place.PlaceType): Place =
        Place("${placeType.labelPrepend()}$label", placeType)

    private fun convertCheckpointEventToInteraction(e: CheckPointEvent) =
        interaction(
            name = "${`package$`.`MODULE$`.checkpointEventInteractionPrefix()}${e.name()}",
            inputIngredients = emptyList(),
            output = listOf(`Event$`.`MODULE$`.apply(e.name(), emptySequence<Ingredient>().asScala)),
            requiredEvents = e.requiredEvents,
            requiredOneOfEvents = e.requiredOneOfEvents
        )

    private fun convertSieveToInteraction(s: Sieve) =
        interaction(
            name = "${`package$`.`MODULE$`.sieveInteractionPrefix()}${s.name()}",
            inputIngredients = s.inputIngredients,
            output = s.output,
            requiredEvents = emptySet(),
            requiredOneOfEvents = emptySet()
        )

    private fun flattenSubRecipesToInteraction(recipe: Recipe): Set<InteractionDescriptor> {
        fun copyInteraction(i: InteractionDescriptor) = Interaction.apply(
            $$"$${`package$`.`MODULE$`.subRecipePrefix()}$${recipe.name()}$$${i.name()}",
            i.inputIngredients(),
            i.output(),
            i.requiredEvents(),
            i.requiredOneOfEvents(),
            i.predefinedIngredients(),
            i.overriddenIngredientNames(),
            i.overriddenOutputIngredientName(),
            i.maximumInteractionCount(),
            i.failureStrategy(),
            i.eventOutputTransformers(),
            i.isReprovider,
            Option.apply(i.originalName())
        )
        return recipe.interactions.map(::copyInteraction).toSet() +
                recipe.checkpointEvents.map(::convertCheckpointEventToInteraction) +
                recipe.subRecipes.flatMap(::flattenSubRecipesToInteraction) +
                recipe.sieves.map(::convertSieveToInteraction)
    }

    private fun flattenSensoryEvents(recipe: Recipe): Set<Event> =
        recipe.sensoryEvents + recipe.subRecipes.flatMap(::flattenSensoryEvents)

    private fun graph(arcs: List<Arc>): Graph<Node, WLDiEdge<Any>> =
        `Graph$`.`MODULE$`.from(
            arcs.map { it as WLDiEdge<Any> }.asScala,
            ClassTag.apply(WLDiEdge::class.java),
            CoreConfig(GraphConfig.defaultOrder(), ArraySet.`Hints$`.`MODULE$`.apply(16, 32, 48, 80))
        ) as Graph<Node, WLDiEdge<Any>>

    private fun <N, L> wlDiEdge(node1: Node, node2: Node, weight: Double, label: L): WLDiEdge<N> =
        `WLDiEdge$`.`MODULE$`.newEdge(GraphEdge.`NodeProduct$`.`MODULE$`.apply(node1, node2), weight, label)
}

fun ingredientToCompiledIngredient(ingredient: Ingredient): IngredientDescriptor =
    IngredientDescriptor(ingredient.name(), ingredient.ingredientType())

fun eventToCompiledEvent(event: Event): EventDescriptor =
    EventDescriptor(
        event.name(),
        event.providedIngredients().map(::ingredientToCompiledIngredient) as Seq<IngredientDescriptor>
    )

fun interactionTransitionOf(
    interactionDescriptor: InteractionDescriptor,
    defaultFailureStrategy: InteractionFailureStrategy,
    allIngredientNames: Set<String>
): InteractionTransition {
    //This transforms the event using the eventOutputTransformer to the new event
    //If there is no eventOutputTransformer for the event the original event is returned
    fun transformEventType(event: Event): Event =
        when (val eventOutputTransformer = interactionDescriptor.eventOutputTransformers[event]) {
            null -> event
            else -> com.ing.baker.recipe.scaladsl.Event(
                eventOutputTransformer.newEventName,
                event.providedIngredients.map { i ->
                    Ingredient(
                        eventOutputTransformer.ingredientRenames.getOrElse(i.name(), { i.name() }),
                        i.ingredientType()
                    )
                }.asScala,
                Option.empty()
            )
        }

    fun transformEventOutputTransformer(recipeEventOutputTransformer: EventOutputTransformer): com.ing.baker.il.EventOutputTransformer =
        com.ing.baker.il.EventOutputTransformer(
            recipeEventOutputTransformer.newEventName(),
            recipeEventOutputTransformer.ingredientRenames()
        )

    fun transformEventToCompiledEvent(event: Event): EventDescriptor =
        EventDescriptor(
            event.name(),
            event.providedIngredients().map(::ingredientToCompiledIngredient) as Seq<IngredientDescriptor>
        )

    // Replace RecipeInstanceId to recipeInstanceIdName tag as know in compiledRecipe
    // Replace BakerMetaData to BakerMetaData tag as know in compiledRecipe
    // Replace BakerEventList to BakerEventList tag as know in compiledRecipe
    // Replace ingredient tags with overridden tags
    val inputFields: Seq<Pair<String, Type>> = interactionDescriptor.inputIngredients
        .map { ingredient ->
            when (ingredient.name()) {
                com.ing.baker.recipe.common.`package$`.`MODULE$`.recipeInstanceIdName() -> ILPackage.recipeInstanceIdName()
                com.ing.baker.recipe.common.`package$`.`MODULE$`.recipeInstanceMetadataName() -> ILPackage.recipeInstanceMetadataName()
                com.ing.baker.recipe.common.`package$`.`MODULE$`.recipeInstanceEventListName() -> ILPackage.recipeInstanceEventListName()
                else -> interactionDescriptor.overriddenIngredientNames()
                    .getOrElse(ingredient.name(), { ingredient.name() })
            } to ingredient.ingredientType()
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
        when (val strategy = interactionDescriptor.failureStrategy().getOrElse { defaultFailureStrategy }) {
            is InteractionFailureStrategy.RetryWithIncrementalBackoff -> {
                val exhaustedRetryEvent = when (val e = strategy.fireRetryExhaustedEvent()) {
                    is Some -> Some(
                        EventDescriptor(
                            e.value().getOrElse { null as String? }
                                ?: (interactionDescriptor.name() + ILPackage.exhaustedEventAppend()),
                            emptyList<IngredientDescriptor>().asScala)
                    )

                    else -> Option.empty()
                }
                val functionalFailedEvent = when (val e = strategy.fireFunctionalEvent()) {
                    is Some -> Some(
                        EventDescriptor(
                            e.value().getOrElse { null as String? }
                                ?: (interactionDescriptor.name() + ILPackage.functionalFailedEventAppend()),
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
                    .getOrElse { interactionDescriptor.name() + ILPackage.exhaustedEventAppend() }
                val exhaustedRetryEvent = EventDescriptor(eventName, emptyList<IngredientDescriptor>().asScala)
                Triple(FireEventAfterFailure(exhaustedRetryEvent), Some(exhaustedRetryEvent), Option.empty())
            }

            is InteractionFailureStrategy.FireEventAndBlock -> {
                val eventName = strategy.eventName()
                    .getOrElse { interactionDescriptor.name() + ILPackage.exhaustedEventAppend() }
                val exhaustedRetryEvent = EventDescriptor(eventName, emptyList<IngredientDescriptor>().asScala)
                Triple(FireEventAfterFailure(exhaustedRetryEvent), Some(exhaustedRetryEvent), Option.empty())
            }

            is InteractionFailureStrategy.FireEventAndResolve -> {
                val eventName = strategy.eventName()
                    .getOrElse { interactionDescriptor.name() + ILPackage.functionalFailedEventAppend() }
                val functionalFailed = EventDescriptor(eventName, emptyList<IngredientDescriptor>().asScala)
                Triple(FireFunctionalEventAfterFailure(functionalFailed), Option.empty(), Some(functionalFailed))
            }

            else -> Triple(`BlockInteraction$`.`MODULE$`, Option.empty(), Option.empty())
        }
    val failureStrategy = p.first
    val exhaustedRetryEvent = p.second.toList().toSeq()
    val functionalRetryEvent = p.third.toList().toSeq()

    // In order to keep compatibility with Scala compiler implementation, we need to use specific Scala collections.
    // Otherwise, generated recipe id's hash would be different between the two implementations, which is not desirable.
    fun concatEvents(first: Seq<EventDescriptor>, vararg rest: Seq<EventDescriptor>): Seq<EventDescriptor> {
        // Handling special case for checkpoint events to keep it compatible with RecipeCompiler Scala implementation.
        return if (interactionDescriptor.isSpecialScalaCaseSeq() || first.isEmpty)
            scala.collection.immutable.`$colon$colon`.from(
                first.toList()
            )
        else
            rest.fold(first.asJava) { acc, list ->
                acc + list.asJava
            }.asScala
    }

    val eventsToFireAll = concatEvents(eventsToFire, exhaustedRetryEvent, functionalRetryEvent)
    val originalEventsAll = concatEvents(originalEvents, exhaustedRetryEvent, functionalRetryEvent)

    // Here the same - keeping recipe id's hash the same as Scala implementation.
    fun requiredIngredients(): Seq<IngredientDescriptor> {
        return if (interactionDescriptor.isSpecialScalaCaseSeq() && inputFields.isEmpty())
            scala.collection.immutable.`Nil$`.`MODULE$` as Seq<IngredientDescriptor>
        else if (interactionDescriptor.isSpecialScalaCaseSeq() || (eventsToFireAll.isEmpty() && originalEventsAll.isEmpty()))
            scala.collection.immutable.List.from(
                inputFields
                    .asJava
                    .map { (name, ingredientType) -> IngredientDescriptor(name, ingredientType) }
                    .asScala
            )
                .`$plus$plus`(scala.collection.immutable.`Nil$`.`MODULE$` as Seq<IngredientDescriptor>) as Seq<IngredientDescriptor>
        else
            inputFields.asJava.map { (name, ingredientType) -> IngredientDescriptor(name, ingredientType) }.asScala
    }

    return InteractionTransition(
        eventsToFireAll,
        originalEventsAll,
        requiredIngredients(),
        interactionDescriptor.name(),
        interactionDescriptor.originalName(),
        predefinedIngredientsWithOptionalsEmpty.asScala,
        interactionDescriptor.maximumInteractionCount(),
        failureStrategy,
        interactionDescriptor.eventOutputTransformers.map { (event, transformer) ->
            event.name() to transformEventOutputTransformer(
                transformer
            )
        }.toMap().asScala,
        interactionDescriptor.isReprovider()
    )
}

private fun InteractionDescriptor.isSpecialScalaCaseSeq() = isCheckpoint() || isSieve() || isSubRecipe()

private fun InteractionDescriptor.isCheckpoint() =
    name().startsWith(`package$`.`MODULE$`.checkpointEventInteractionPrefix())

private fun InteractionDescriptor.isSieve() =
    name().startsWith("SieveInteraction") ||
            name().startsWith(`package$`.`MODULE$`.sieveInteractionPrefix())

private fun InteractionDescriptor.isSubRecipe() =
    name().startsWith(`package$`.`MODULE$`.subRecipePrefix())

private fun interaction(
    name: String?,
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
    Interaction.apply(
        name,
        inputIngredients.asScala,
        output.asScala,
        requiredEvents.asScala,
        requiredOneOfEvents.map { it: Set<String> -> it.asScala }.toSet().asScala,
        predefinedIngredients.asScala,
        overriddenIngredientNames.asScala,
        Option.apply(overriddenOutputIngredientName),
        Option.apply(maximumInteractionCount),
        Option.apply(failureStrategy),
        eventOutputTransformers.asScala,
        isReprovider,
        Option.apply(oldName)
    )

val Recipe.sensoryEvents get() = this.sensoryEvents().asJava
val Recipe.interactions get() = this.interactions().asJava
val Recipe.subRecipes get() = this.subRecipes().asJava
val Recipe.checkpointEvents get() = this.checkpointEvents().asJava
val Recipe.sieves get() = this.sieves().asJava
val InteractionDescriptor.requiredEvents get() = this.requiredEvents().asJava
val InteractionDescriptor.requiredOneOfEvents get() = this.requiredOneOfEvents().asJava.map { it.asJava }.toSet()
val InteractionDescriptor.output get() = this.output().asJava
val InteractionDescriptor.eventOutputTransformers get() = this.eventOutputTransformers().asJava
val InteractionDescriptor.inputIngredients get() = this.inputIngredients().asJava
val InteractionDescriptor.predefinedIngredients get() = this.predefinedIngredients().asJava
val InteractionTransition.eventsToFire get() = this.eventsToFire().asJava
val InteractionTransition.nonProvidedIngredients get() = this.nonProvidedIngredients().asJava
val InteractionTransition.maximumInteractionCount
    get(): Int? = this.maximumInteractionCount().getOrElse { null as Int? }
val Event.providedIngredients get() = this.providedIngredients().asJava
val EventDescriptor.ingredients get() = this.ingredients().asJava
val EventOutputTransformer.ingredientRenames get() = this.ingredientRenames().asJava
val EventOutputTransformer.newEventName: String? get() = this.newEventName()
val CheckPointEvent.requiredOneOfEvents get() = this.requiredOneOfEvents().asJava.map { it.asJava }.toSet()
val CheckPointEvent.requiredEvents get() = this.requiredEvents().asJava
val Sieve.inputIngredients get() = this.inputIngredients().asJava
val Sieve.output get() = this.output().asJava
