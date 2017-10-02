package com.ing.baker
package compiler

import com.ing.baker.il.RecipeValidations.postCompileValidations
import com.ing.baker.il.petrinet.Place._
import com.ing.baker.il.petrinet._
import com.ing.baker.il.{CompiledRecipe, EventType, ValidationSettings}
import com.ing.baker.petrinet.api._
import com.ing.baker.recipe.common._

import scala.collection.mutable
import scala.language.postfixOps
import scalax.collection.immutable.Graph

object RecipeCompiler {

  implicit class TupleSeqOps[A, B](seq: Seq[(Seq[A], Seq[B])]) {
    def unzipFlatten: (Seq[A], Seq[B]) = seq.unzip match {
      case (a, b) => (a.flatten, b.flatten)
    }
  }

  /**
    * Creates a transition for a missing event in the recipe.
    */
  private def missingEventTransition[E](event: EventType): MissingEventTransition[E] = MissingEventTransition[E](event.name)

  private def buildEventAndPreconditionArcs(
                                             interaction: InteractionDescriptor,
                                             preconditionTransition: EventType => Option[Transition[_, _]],
                                             interactionTransition: String => Option[Transition[_, _]]): (Seq[Arc], Seq[String]) = {

    interaction.requiredEvents.toSeq.map { event =>
      // a new `Place` generated for each AND events
      val eventPreconditionPlace = createPlace(label = s"${event.name}-${interaction.name}", placeType = EventPreconditionPlace)

      buildEventPreconditionArcs(eventToCompiledEvent(event),
        eventPreconditionPlace,
        preconditionTransition,
        interactionTransition(interaction.name).get)
    }.unzipFlatten
  }

  private def buildEventORPreconditionArcs(
                                            interaction: InteractionDescriptor,
                                            preconditionTransition: EventType => Option[Transition[_, _]],
                                            interactionTransition: String => Option[Transition[_, _]]): (Seq[Arc], Seq[String]) = {

    // only one `Place` for all the OR events
    val eventPreconditionPlace = createPlace(label = interaction.name, placeType = EventOrPreconditionPlace)

    interaction.requiredOneOfEvents.toSeq.map { event =>
      buildEventPreconditionArcs(eventToCompiledEvent(event),
        eventPreconditionPlace,
        preconditionTransition,
        interactionTransition(interaction.name).get)
    }.unzipFlatten
  }

  private def buildEventPreconditionArcs(
                                          event: EventType,
                                          preconditionPlace: Place[_],
                                          preconditionTransition: EventType => Option[Transition[_, _]],
                                          interactionTransition: Transition[_, _]): (Seq[Arc], Seq[String]) = {

    val eventTransition = preconditionTransition(event)

    val notProvidedError = eventTransition match {
      case None => Seq(s"Event '$event' for '$interactionTransition' is not provided in the recipe")
      case Some(_) => Seq.empty
    }

    val arcs = Seq(
      arc(eventTransition.getOrElse(missingEventTransition(event)), preconditionPlace, 1),
      arc(preconditionPlace, interactionTransition, 1)
    )

    (arcs, notProvidedError)
  }

  // the (possible) event output arcs / places
  private def interactionEventOutputArc(interaction: InteractionTransition[_],
                                        events: Seq[EventType],
                                        findInternalEventByEvent: EventType => Option[Transition[_, _]]): Seq[Arc] = {
    val resultPlace = createPlace(label = interaction.label, placeType = InteractionEventOutputPlace)
    if (interaction.eventsToFire.nonEmpty) {
      val eventArcs = events.map { event =>
        val internalEventTransition = findInternalEventByEvent(event).get
        val filter = (value: Any) => value == event.name
        arc(resultPlace, internalEventTransition, 1, filter)
      }
      arc(interaction, resultPlace, 1) +: eventArcs
    }
    else Seq.empty
  }

  // the (possible) data output arcs / places
  private def interactionIngredientOutputArc(t: InteractionTransition[_], ingredientName: String): Seq[Arc] =
    Seq(arc(t, createPlace(ingredientName, IngredientPlace), 1))

  /**
    * Draws an arc from all required ingredients for an interaction
    * If the ingredient has multiple consumers create a multi transition place and create both arcs for it
    */
  private def buildInteractionInputArcs(
                                         t: InteractionTransition[_],
                                         multipleConsumerFacilitatorTransitions: Seq[Transition[_, _]],
                                         ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition[_]]]): Seq[Arc] = {

    val (fieldNamesWithPrefixMulti, fieldNamesWithoutPrefix) =
      t.nonProvidedIngredients.keySet.toSeq.partition(ingredientsWithMultipleConsumers.contains)

    // the extra arcs to model multiple output transitions from one place
    val internalDataInputArcs = fieldNamesWithPrefixMulti flatMap { fieldName =>
      val multiTransitionPlace = createPlace(s"${t.label}-$fieldName", placeType = MultiTransitionPlace)
      Seq(
        // one arc from multiplier place to the transition
        arc(getMultiTransition(fieldName, multipleConsumerFacilitatorTransitions),
          multiTransitionPlace,
          1),
        // one arc from extra added place to transition
        arc(multiTransitionPlace, t, 1))
    }

    // the data input arcs / places
    val dataInputArcs = fieldNamesWithoutPrefix.map(fieldName => arc(createPlace(fieldName, IngredientPlace), t, 1))

    val limitInteractionCountArc =
      t.maximumInteractionCount.map(n => arc(createPlace(s"limit:${t.label}", FiringLimiterPlace(n)), t, 1))

    dataInputArcs ++ internalDataInputArcs ++ limitInteractionCountArc
  }

  private def buildInteractionOutputArcs(t: InteractionTransition[_],
                                         findInternalEventByEvent: EventType => Option[Transition[_, _]]): Seq[Arc] = {
    interactionEventOutputArc(t, t.eventsToFire, findInternalEventByEvent)
  }

  private def buildInteractionArcs(
                                    multipleOutputFacilitatorTransitions: Seq[Transition[_, _]],
                                    placeNameWithDuplicateTransitions: Map[String, Seq[InteractionTransition[_]]],
                                    findInternalEventByEvent: EventType => Option[Transition[_, _]])(
                                    t: InteractionTransition[_]): Seq[Arc] = {

    buildInteractionInputArcs(
      t,
      multipleOutputFacilitatorTransitions,
      placeNameWithDuplicateTransitions) ++ buildInteractionOutputArcs(t, findInternalEventByEvent)
  }

  /**
    * Compile the given recipe to a technical recipe that is useful for Baker.
    *
    * @param recipe             ; The Recipe to compile and execute
    * @param validationSettings The validation settings to follow for the validation
    * @return
    */
  def compileRecipe(recipe: Recipe,
                    validationSettings: ValidationSettings): CompiledRecipe = {

    val precompileErrors: Seq[String] = preCompileAssertions(recipe)

    //All ingredient names provided by sensory events or by interactions
    val allIngredientNames: Set[String] =
      recipe.sensoryEvents.flatMap(e => e.providedIngredients.map(i => i.name)) ++
        (recipe.interactions ++ recipe.sieves).flatMap(i => i.interaction.output match {
          case pi: ProvidesIngredient => Set(i.overriddenOutputIngredientName.getOrElse(pi.ingredient.name))
          case fi: FiresOneOfEvents => fi.events.flatMap { e =>
            // check if the event was renamed (check if there is a transformer for this event)
            i.eventOutputTransformers.get(e) match {
              case Some(transformer) => e.providedIngredients.map(ingredient => transformer.ingredientRenames.getOrElse(ingredient.name, ingredient.name))
              case None => e.providedIngredients.map(_.name)
            }
          }
          case ProvidesNothing => Set.empty
        })

    val actionDescriptors: Seq[InteractionDescriptor] = recipe.interactions ++ recipe.sieves

    // For inputs for which no matching output cannot be found, we do not want to generate a place.
    // It should be provided at runtime from outside the active petri net (marking)
    val interactionTransitions = recipe.interactions.map(_.toInteractionTransition(recipe.defaultFailureStrategy, allIngredientNames))

    val sieveTransitions = recipe.sieves.map(_.toSieveTransition(recipe.defaultFailureStrategy, allIngredientNames))

    val allInteractionTransitions: Seq[InteractionTransition[_]] = sieveTransitions ++ interactionTransitions

    // events provided from outside
    val sensoryEventTransitions: Seq[EventTransition] = recipe.sensoryEvents.map { event => EventTransition(eventToCompiledEvent(event), isSensoryEvent = true, event.maxFiringLimit) }.toSeq

    // events provided by other transitions / actions
    val interactionEventTransitions: Seq[EventTransition] = allInteractionTransitions.flatMap { t =>
      t.eventsToFire.map(event => EventTransition(event, isSensoryEvent = false))
    }

    val allEventTransitions: Seq[EventTransition] = sensoryEventTransitions ++ interactionEventTransitions

    // Given the event classes, it is creating the ingredient places and
    // connecting a transition to a ingredient place.
    val internalEventArcs: Seq[Arc] = allInteractionTransitions.flatMap { t =>
      t.eventsToFire.flatMap { event =>
        event.ingredientTypes.map(ingredient =>
          arc(interactionEventTransitions.getByLabel(event.name), createPlace(ingredient.name, IngredientPlace), 1))
      }
    }

    val eventLimiterArcs: Seq[Arc] = sensoryEventTransitions.flatMap(
      t => t.maxFiringLimit match {
        case Some(n) => Seq(arc(createPlace(s"limit:${t.label}", FiringLimiterPlace(n)), t, 1))
        case None => Seq.empty
      }
    )

    // This generates precondition arcs for Required Events (AND).
    val (eventPreconditionArcs, preconditionANDErrors) = actionDescriptors.map { t =>
      buildEventAndPreconditionArcs(t,
        allEventTransitions.findEventTransitionsByEvent,
        allInteractionTransitions.findTransitionByName)
    }.unzipFlatten

    // This generates precondition arcs for Required Events (OR).
    val (eventOrPreconditionArcs, preconditionORErrors) = actionDescriptors.map { t =>
      buildEventORPreconditionArcs(t,
        allEventTransitions.findEventTransitionsByEvent,
        allInteractionTransitions.findTransitionByName)
    }.unzipFlatten

    val (sensoryEventWithoutIngredients, sensoryEventWithIngredients) = sensoryEventTransitions.partition(_.event.ingredientTypes.isEmpty)

    // It connects a sensory event to an ingredient places
    val sensoryEventArcs: Seq[Arc] = sensoryEventWithIngredients
      .flatMap(et => et.event.ingredientTypes.map(ingredient => arc(et, createPlace(ingredient.name, IngredientPlace), 1)))

    val eventThatArePreconditions: Seq[String] =
      actionDescriptors.flatMap {
        actionDescriptor => actionDescriptor.requiredEvents.map(_.name) ++ actionDescriptor.requiredOneOfEvents.map(_.name)
      }

    // It connects a sensory event to a dummy ingredient so it can be modelled into the Petri net
    val sensoryEventArcsNoIngredientsArcs: Seq[Arc] = sensoryEventWithoutIngredients
      //Filter out events that are preconditions to interactions
      .filterNot(sensoryEvent => eventThatArePreconditions.contains(sensoryEvent.label))
      .map(sensoryEvent => arc(sensoryEvent, createPlace(sensoryEvent.label, EmptyEventIngredientPlace), 1))

    // First find the cases where multiple transitions depend on the same ingredient place
    val ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition[_]]] =
      getIngredientsWithMultipleConsumers(allInteractionTransitions)

    // Add one new transition for each duplicate input (the newly added one in the image above)
    val multipleConsumerFacilitatorTransitions: Seq[Transition[_, _]] =
      ingredientsWithMultipleConsumers.keys
        .map(name => MultiFacilitatorTransition(label = name))
        .toSeq

    val multipleOutputFacilitatorArcs: Seq[Arc] =
      multipleConsumerFacilitatorTransitions.map(t =>
        arc(createPlace(t.label, IngredientPlace), t, 1))

    val interactionArcs: Seq[Arc] =
      allInteractionTransitions.flatMap(
        buildInteractionArcs(multipleConsumerFacilitatorTransitions,
          ingredientsWithMultipleConsumers,
          interactionEventTransitions.findEventTransitionsByEvent))

    val arcs = (interactionArcs
      ++ eventPreconditionArcs
      ++ eventOrPreconditionArcs
      ++ eventLimiterArcs
      ++ sensoryEventArcs
      ++ sensoryEventArcsNoIngredientsArcs
      ++ internalEventArcs
      ++ multipleOutputFacilitatorArcs)

    val petriNet: ScalaGraphPetriNet[Place[_], Transition[_, _]] = new ScalaGraphPetriNet(Graph(arcs: _*))

    val initialMarking: Marking[Place] = petriNet.places.collect {
      case p@Place(_, FiringLimiterPlace(n)) => p -> Map(() -> n)
    }.toMarking

    val compiledRecipe = CompiledRecipe(
      name = recipe.name,
      petriNet = petriNet,
      initialMarking = initialMarking,
      sensoryEvents = recipe.sensoryEvents.map(eventToCompiledEvent),
      validationErrors = preconditionORErrors ++ preconditionANDErrors ++ precompileErrors,
      eventReceivePeriod = recipe.eventReceivePeriod,
      retentionPeriod = recipe.retentionPeriod
    )

    postCompileValidations(compiledRecipe, validationSettings)
  }

  def compileRecipe(recipe: Recipe): CompiledRecipe = compileRecipe(recipe, ValidationSettings.defaultValidationSettings)

  private def getMultiTransition(internalRepresentationName: String,
                                 transitions: Seq[Transition[_, _]]): Transition[_, _] = {
    transitions
      .find(t => t.label.equals(internalRepresentationName))
      .getOrElse(throw new NoSuchElementException(s"No multi transition found with name $internalRepresentationName"))
  }

  /**
    * Obtains a map of each input place name that is used multiple times and the reflected transitions using it.
    *
    * @param actionTransitions Seq of reflected transition.
    * @return A map from input place name to reflected transitions (where the transitions have as input the place).
    */
  private def getIngredientsWithMultipleConsumers(actionTransitions: Seq[InteractionTransition[_]]): Map[String, Seq[InteractionTransition[_]]] = {
    // Obtain a list of field name with their transition
    val placeNameWithTransition: Seq[(String, InteractionTransition[_])] = for {
      transition <- actionTransitions
      inputPlaceName <- transition.nonProvidedIngredients.keySet
    } yield (inputPlaceName, transition)

    // Then obtain the places with multiple out-adjacent transitions
    val ingredientsWithMultipleConsumers = placeNameWithTransition.groupBy {
      case (placeName, _) => placeName
    } // Group by place name
      .filter { case (_, interactions) => interactions.size >= 2 } // Only keep those place names which have more than one out-adjacent transition
      .map { case (placeName, interactions) => (placeName, interactions.map(_._2)) } // Cleanup the data structure

    ingredientsWithMultipleConsumers
  }

  private def createPlace(label: String, placeType: PlaceType): Place[Any] = Place(label = s"${placeType.labelPrepend}$label", placeType)

  private def assertNoDuplicateElementsExist[T](compareIdentifier: T => Any, elements: Set[T]) = elements.foreach { e =>
    (elements - e).find(c => compareIdentifier(c) == compareIdentifier(e)).foreach { c => throw new IllegalStateException(s"Duplicate identifiers found: ${e.getClass.getSimpleName}:$e and ${c.getClass.getSimpleName}:$c") }
  }

  private def assertValidNames[T](nameFunc: T => String, list: Iterable[T], typeName: String) = list.map(nameFunc).filter(name => name == null || name.isEmpty).foreach { _ =>
    throw new IllegalArgumentException(s"$typeName with a null or empty name found")
  }

  private def assertNonEmptyRecipe(recipe: Recipe): Seq[String] = {
    val errors = mutable.MutableList.empty[String]
    if (recipe.sensoryEvents.isEmpty)
      errors += "No sensory events found."
    if (recipe.interactions.size + recipe.sieves.size == 0)
      errors += "No interactions or sieves found."
    errors
  }

  private def preCompileAssertions(recipe: Recipe): Seq[String] = {
    assertValidNames[Recipe](_.name, Seq(recipe), "Recipe")
    assertValidNames[InteractionDescriptor](_.name, recipe.interactions, "Interaction")
    assertValidNames[InteractionDescriptor](_.name, recipe.sieves, "Sieve Interaction")
    assertValidNames[Event](_.name, recipe.sensoryEvents, "Event")
    val allIngredients = recipe.sensoryEvents.flatMap(_.providedIngredients) ++ recipe.interactions.flatMap(_.interaction.inputIngredients) ++ recipe.sieves.flatMap(_.interaction.inputIngredients)
    assertValidNames[Ingredient](_.name, allIngredients, "Ingredient")
    assertNoDuplicateElementsExist[InteractionDescriptor](_.name, recipe.interactions.toSet ++ recipe.sieves.toSet)
    assertNoDuplicateElementsExist[Event](_.name, recipe.sensoryEvents)
    assertNonEmptyRecipe(recipe)
  }
}
