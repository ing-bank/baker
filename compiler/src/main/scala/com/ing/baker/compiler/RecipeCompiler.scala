package com.ing.baker
package compiler

import com.ing.baker.il.RecipeValidations.postCompileValidations
import com.ing.baker.il.petrinet.Place._
import com.ing.baker.il.petrinet._
import com.ing.baker.il.{CompiledRecipe, EventDescriptor, ValidationSettings}
import com.ing.baker.petrinet.api._
import com.ing.baker.recipe.common._
import scalax.collection.immutable.Graph

import scala.language.postfixOps

object RecipeCompiler {

  implicit class TupleSeqOps[A, B](seq: Seq[(Seq[A], Seq[B])]) {
    def unzipFlatten: (Seq[A], Seq[B]) = seq.unzip match {
      case (a, b) => (a.flatten, b.flatten)
    }
  }

  /**
    * Creates a transition for a missing event in the recipe.
    */
  private def missingEventTransition[E](eventName: String): MissingEventTransition = MissingEventTransition(eventName)

  private def buildEventAndPreconditionArcs(interaction: InteractionDescriptor,
                                            preconditionTransition: String => Option[Transition],
                                            interactionTransition: String => Option[Transition]): (Seq[Arc], Seq[String]) = {

    //Find the event in available events

    interaction.requiredEvents.toSeq.map { eventName =>
      // a new `Place` generated for each AND events
      val eventPreconditionPlace = createPlace(label = s"$eventName-${interaction.name}", placeType = EventPreconditionPlace)

      buildEventPreconditionArcs(eventName,
        eventPreconditionPlace,
        preconditionTransition,
        interactionTransition(interaction.name).get)
    }.unzipFlatten
  }

  private def buildEventORPreconditionArcs(interaction: InteractionDescriptor,
                                           preconditionTransition: String => Option[Transition],
                                           interactionTransition: String => Option[Transition]): (Seq[Arc], Seq[String]) = {

    interaction.requiredOneOfEvents.toSeq.zipWithIndex.map { case (orGroup: Set[String], index: Int) =>
      // only one `Place` for all the OR events
      val eventPreconditionPlace = createPlace(label = s"${interaction.name}-or-$index", placeType = EventOrPreconditionPlace)

      orGroup.toSeq.map { eventName =>
        buildEventPreconditionArcs(eventName,
          eventPreconditionPlace,
          preconditionTransition,
          interactionTransition(interaction.name).get)
      }.unzipFlatten
    }.unzipFlatten
  }

  private def buildEventPreconditionArcs(eventName: String,
                                         preconditionPlace: Place[_],
                                         preconditionTransition: String => Option[Transition],
                                         interactionTransition: Transition): (Seq[Arc], Seq[String]) = {

    val eventTransition = preconditionTransition(eventName)

    val notProvidedError = eventTransition match {
      case None => Seq(s"Event '$eventName' for '$interactionTransition' is not provided in the recipe")
      case Some(_) => Seq.empty
    }

    val arcs = Seq(
      arc(eventTransition.getOrElse(missingEventTransition(eventName)), preconditionPlace, 1),
      arc(preconditionPlace, interactionTransition, 1)
    )

    (arcs, notProvidedError)
  }

  // the (possible) event output arcs / places
  private def buildInteractionOutputArcs(interaction: InteractionTransition): Seq[Arc] = {
    val resultPlace = createPlace(label = interaction.label, placeType = InteractionEventOutputPlace)
    if (interaction.eventsToFire.nonEmpty) {
      val eventArcs = interaction.eventsToFire.flatMap { event =>
        val eventCombinerPlace: Place[_] = createPlace(label = event.name, placeType = IntermediatePlace)
        //Create a new intermediate transition
        val interactionToEventTransition: IntermediateTransition = IntermediateTransition(s"${interaction.interactionName}:${event.name}")
        //link the new transition to the event input place
        val intermediateTransitionToEventCombinerPlace: Arc = arc(interactionToEventTransition, eventCombinerPlace, 1)
        //link the interaction output place to the interactionTransition
        val interactionOutputPlaceToInteramediateTransition: Arc = arc(resultPlace, interactionToEventTransition, 1, Some(event.name))
        Seq(intermediateTransitionToEventCombinerPlace, interactionOutputPlaceToInteramediateTransition)
      }
      arc(interaction, resultPlace, 1) +: eventArcs
    }
    else Seq.empty
  }

  /**
    * Draws an arc from all required ingredients for an interaction
    * If the ingredient has multiple consumers create a multi transition place and create both arcs for it
    */
  private def buildInteractionInputArcs(t: InteractionTransition,
                                        multipleConsumerFacilitatorTransitions: Seq[Transition],
                                        ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition]]): Seq[Arc] = {

    val (fieldNamesWithPrefixMulti, fieldNamesWithoutPrefix) =
      t.nonProvidedIngredients.map(_.name).partition(ingredientsWithMultipleConsumers.contains)

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

  private def buildInteractionArcs(multipleOutputFacilitatorTransitions: Seq[Transition],
                                   placeNameWithDuplicateTransitions: Map[String, Seq[InteractionTransition]])
                                  (t: InteractionTransition): Seq[Arc] = {
    buildInteractionInputArcs(
      t,
      multipleOutputFacilitatorTransitions,
      placeNameWithDuplicateTransitions) ++ buildInteractionOutputArcs(t)
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

    val precompileErrors: Seq[String] = Assertions.preCompileAssertions(recipe)

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

    val sieveTransitions = recipe.sieves.map(_.toInteractionTransition(recipe.defaultFailureStrategy, allIngredientNames))

    val allInteractionTransitions: Seq[InteractionTransition] = sieveTransitions ++ interactionTransitions

    // events provided from outside
    val sensoryEventTransitions: Seq[EventTransition] = recipe.sensoryEvents.map {
      event => EventTransition(eventToCompiledEvent(event), isSensoryEvent = true, event.maxFiringLimit)
    }.toSeq

    // events provided by other transitions / actions
    val interactionEventTransitions: Seq[EventTransition] = allInteractionTransitions.flatMap { t =>
      t.eventsToFire.map(event => EventTransition(event, isSensoryEvent = false))
    }

    val allEventTransitions: Seq[EventTransition] = sensoryEventTransitions ++ interactionEventTransitions

    // Given the event classes, it is creating the ingredient places and
    // connecting a transition to a ingredient place.
    val internalEventArcs: Seq[Arc] = allInteractionTransitions.flatMap { t =>
      t.eventsToFire.flatMap { event =>
        event.ingredients.map { ingredient =>
          val from = interactionEventTransitions.find(_.label == event.name).get
          arc(from, createPlace(ingredient.name, IngredientPlace), 1)
        }
      }
    }

    //Create event limiter places so that events can only fire x amount of times.
    val eventLimiterArcs: Seq[Arc] = sensoryEventTransitions.flatMap(
      t => t.maxFiringLimit match {
        case Some(n) => Seq(arc(createPlace(s"limit:${t.label}", FiringLimiterPlace(n)), t, 1))
        case None => Seq.empty
      }
    )

    def findEventTransitionByEventName(eventName: String) = allEventTransitions.find(_.event.name == eventName)

    def findInteractionByLabel(label: String) = allInteractionTransitions.find(_.label == label)


    //Create events combiner input places
    val eventInputArcs: Seq[Arc] = interactionEventTransitions.flatMap(
      (event: EventTransition) => Seq(arc(createPlace(event.label, IntermediatePlace), event, 1))
    )

    // This generates precondition arcs for Required Events (AND).
    val (eventPreconditionArcs, preconditionANDErrors) = actionDescriptors.map { t =>
      buildEventAndPreconditionArcs(t,
        findEventTransitionByEventName,
        findInteractionByLabel)
    }.unzipFlatten

    // This generates precondition arcs for Required Events (OR).
    val (eventOrPreconditionArcs, preconditionORErrors) = actionDescriptors.map { t =>
      buildEventORPreconditionArcs(t,
        findEventTransitionByEventName,
        findInteractionByLabel)
    }.unzipFlatten

    val (sensoryEventWithoutIngredients, sensoryEventWithIngredients) = sensoryEventTransitions.partition(_.event.ingredients.isEmpty)

    // It connects a sensory event to an ingredient places
    val sensoryEventArcs: Seq[Arc] = sensoryEventWithIngredients
      .flatMap(et => et.event.ingredients.map(ingredient => arc(et, createPlace(ingredient.name, IngredientPlace), 1)))

    val eventThatArePreconditions: Seq[String] =
      actionDescriptors.flatMap {
        actionDescriptor => actionDescriptor.requiredEvents ++ actionDescriptor.requiredOneOfEvents.flatten
      }

    // It connects a sensory event to a dummy ingredient so it can be modelled into the Petri net
    val sensoryEventArcsNoIngredientsArcs: Seq[Arc] = sensoryEventWithoutIngredients
      //Filter out events that are preconditions to interactions
      .filterNot(sensoryEvent => eventThatArePreconditions.contains(sensoryEvent.label))
      .map(sensoryEvent => arc(sensoryEvent, createPlace(sensoryEvent.label, EmptyEventIngredientPlace), 1))

    // First find the cases where multiple transitions depend on the same ingredient place
    val ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition]] =
      getIngredientsWithMultipleConsumers(allInteractionTransitions)

    // Add one new transition for each duplicate input (the newly added one in the image above)
    val multipleConsumerFacilitatorTransitions: Seq[Transition] =
      ingredientsWithMultipleConsumers.keys
        .map(name => MultiFacilitatorTransition(label = name))
        .toSeq

    val multipleOutputFacilitatorArcs: Seq[Arc] =
      multipleConsumerFacilitatorTransitions.map(t =>
        arc(createPlace(t.label, IngredientPlace), t, 1))

    val interactionArcs: Seq[Arc] =
      allInteractionTransitions.flatMap(
        buildInteractionArcs(multipleConsumerFacilitatorTransitions,
          ingredientsWithMultipleConsumers))

    val arcs = (interactionArcs
      ++ eventInputArcs
      ++ eventPreconditionArcs
      ++ eventOrPreconditionArcs
      ++ eventLimiterArcs
      ++ sensoryEventArcs
      ++ sensoryEventArcsNoIngredientsArcs
      ++ internalEventArcs
      ++ multipleOutputFacilitatorArcs)

    val petriNet: PetriNet[Place[_], Transition] = PetriNet(Graph(arcs: _*))

    val initialMarking: Marking[Place] = petriNet.places.collect {
      case p@Place(_, FiringLimiterPlace(n)) => p -> Map((null, n))
    }.toMarking

    val compiledRecipe = CompiledRecipe(
      name = recipe.name,
      petriNet = petriNet,
      initialMarking = initialMarking,
      validationErrors = preconditionORErrors ++ preconditionANDErrors ++ precompileErrors,
      eventReceivePeriod = recipe.eventReceivePeriod,
      retentionPeriod = recipe.retentionPeriod
    )

    postCompileValidations(compiledRecipe, validationSettings)
  }

  def compileRecipe(recipe: Recipe): CompiledRecipe = compileRecipe(recipe, ValidationSettings.defaultValidationSettings)

  private def getMultiTransition(internalRepresentationName: String,
                                 transitions: Seq[Transition]): Transition = {
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
  private def getIngredientsWithMultipleConsumers(actionTransitions: Seq[InteractionTransition]): Map[String, Seq[InteractionTransition]] = {
    // Obtain a list of field name with their transition
    val placeNameWithTransition: Seq[(String, InteractionTransition)] = for {
      transition <- actionTransitions
      inputPlaceName <- transition.nonProvidedIngredients.map(_.name)
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
}
