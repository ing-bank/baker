package com.ing.baker
package compiler

import com.ing.baker.compiledRecipe.ingredientExtractors.{CompositeIngredientExtractor, IngredientExtractor}
import com.ing.baker.compiledRecipe.petrinet.Place._
import com.ing.baker.compiledRecipe.petrinet.ProvidesType.{ProvidesEvent, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.compiledRecipe.petrinet._
import com.ing.baker.compiledRecipe.{CompiledRecipe, RecipeValidations, ValidationSettings}
import com.ing.baker.core.{BakerException, ProcessState}
import com.ing.baker.recipe.common.{InteractionDescriptor, Recipe}
import io.kagera.api._

import scala.language.postfixOps

object RecipeCompiler {

  implicit class TupleSeqOps[A, B](seq: Seq[(Seq[A], Seq[B])]) {
    def unzipFlatten: (Seq[A], Seq[B]) = seq.unzip match { case (a, b) => (a.flatten, b.flatten) }
  }

  /**
    * Creates a transition for a missing event in the recipe.
    */
  private def missingEventTransition[E](clazz: Class[E]): MissingEventTransition[E] = MissingEventTransition[E](clazz.getSimpleName.hashCode, clazz.getSimpleName)

  private def buildEventAndPreconditionArcs(
      interaction: InteractionDescriptor[_],
      preconditionTransition: Class[_] => Option[Transition[_, _, _]],
      interactionTransition: String => Option[Transition[_, _, _]]): (Seq[Arc], Seq[String]) = {

    interaction.requiredEvents.toSeq.map { eventClass =>
      // a new `Place` generated for each AND events
      val eventPreconditionPlace = createPlace(label = eventClass.getSimpleName, placeType = EventPreconditionPlace)

      buildEventPreconditionArcs(eventClass,
                                 eventPreconditionPlace,
                                 preconditionTransition,
                                 interactionTransition(interaction.name).get)
    }.unzipFlatten
  }

  private def buildEventORPreconditionArcs(
      interaction: InteractionDescriptor[_],
      preconditionTransition: Class[_] => Option[Transition[_, _, _]],
      interactionTransition: String => Option[Transition[_, _, _]]): (Seq[Arc], Seq[String]) = {

    // only one `Place` for all the OR events
    val eventPreconditionPlace = createPlace(label = interaction.name, placeType = EventOrPreconditionPlace)

    interaction.requiredOneOfEvents.toSeq.map { eventClass =>
      buildEventPreconditionArcs(eventClass,
                                 eventPreconditionPlace,
                                 preconditionTransition,
                                 interactionTransition(interaction.name).get)
    }.unzipFlatten
  }

  private def buildEventPreconditionArcs(
      eventClass: Class[_],
      preconditionPlace: Place[_],
      preconditionTransition: Class[_] => Option[Transition[_, _, _]],
      interactionTransition: Transition[_, _, _]): (Seq[Arc], Seq[String]) = {

    val eventTransition = preconditionTransition(eventClass)

    val notProvidedError = eventTransition.isEmpty.toOption {
      s"Event '$eventClass' for '$interactionTransition' is not provided in the recipe"
    }.toSeq

    val arcs = Seq(
      arc(eventTransition.getOrElse(missingEventTransition(eventClass)), preconditionPlace, 1),
      arc(preconditionPlace, interactionTransition, 1)
    )

    (arcs, notProvidedError)
  }

  // the (possible) event output arcs / places
  private def interactionEventOutputArc(interaction: InteractionTransition[_],
                                        findInternalEventByClass: Class[_] => Option[Transition[_, _, _]]): Seq[Arc] = {
    interaction.providesType match {
      case e: ProvidesEvent => {
        val resultPlace = createPlace(label = interaction.label, placeType = InteractionEventOutputPlace)
        val eventArcs = e.outputEventClasses.map { eventClass =>
          val internalEventTransition = findInternalEventByClass(eventClass).get
          val filter                  = (value: Any) => value == eventClass.getSimpleName
          arc(resultPlace, internalEventTransition, 1, filter)
        }
        arc(interaction, resultPlace, 1) +: eventArcs
      }
      case _ => throw new BakerException("InteractionEventOutputArc called for non event transition")
    }
  }

  // the (possible) data output arcs / places
  private def interactionIngredientOutputArc(t: InteractionTransition[_]): Seq[Arc] =
    t.providesType match {
      case i: ProvidesIngredient => Seq(i.outputIngredient._1).map(name => createPlace(name, IngredientPlace)).map(p => arc(t, p, 1))
      case _ => Seq.empty
    }

  /**
    * Draws an arc from all required ingredients for an interaction
    * If the ingredient has multiple consumers create a multi transition place and create both arcs for it
    * @param t
    * @param multipleConsumerFacilitatorTransitions
    * @param ingredientsWithMultipleConsumers
    * @return
    */
  private def buildInteractionInputArcs(
      t: InteractionTransition[_],
      multipleConsumerFacilitatorTransitions: Seq[Transition[_, _, _]],
      ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition[_]]]): Seq[Arc] = {

    val (fieldNamesWithPrefixMulti, fieldNamesWithoutPrefix) =
      t.requiredIngredientNames.toSeq.partition(ingredientsWithMultipleConsumers.contains)

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
      t.maximumInteractionCount.map(_ => arc(createPlace(s"limit:${t.label}", FiringLimiterPlace), t, 1))

    dataInputArcs ++ internalDataInputArcs ++ limitInteractionCountArc
  }

  private def buildInteractionOutputArcs(t: InteractionTransition[_],
                                         findInternalEventByClass: Class[_] => Option[Transition[_, _, _]]): Seq[Arc] = {
    t.providesType match {
      case e: ProvidesEvent => interactionEventOutputArc(t, findInternalEventByClass)
      case i: ProvidesIngredient => interactionIngredientOutputArc(t)
      case n: ProvidesNothing.type => interactionIngredientOutputArc(t)
    }
  }

  private def buildInteractionArcs(
      multipleOutputFacilitatorTransitions: Seq[Transition[_, _, _]],
      placeNameWithDuplicateTransitions: Map[String, Seq[InteractionTransition[_]]],
      findInternalEventByClass: Class[_] => Option[Transition[_, _, _]])(
      t: InteractionTransition[_]): Seq[Arc] = {

    buildInteractionInputArcs(
      t,
      multipleOutputFacilitatorTransitions,
      placeNameWithDuplicateTransitions) ++ buildInteractionOutputArcs(t, findInternalEventByClass)
  }

  val defaultIngredientExtractor: IngredientExtractor = new CompositeIngredientExtractor()

  /**
    * Compile the given recipe to a technical recipe that is useful for Baker.
    *
    * @param recipe; The Recipe to compile and execute
    * @param validationSettings The validation settings to follow for the validation
    * @return
    */
  def compileRecipe(recipe: Recipe,
                    validationSettings: ValidationSettings,
                    ingredientExtractor: IngredientExtractor): CompiledRecipe = {

    val actionDescriptors: Seq[InteractionDescriptor[_]] = recipe.interactionDescriptors ++ recipe.sieveDescriptors

    // For inputs for which no matching output cannot be found, we do not want to generate a place.
    // It should be provided at runtime from outside the active petri net (marking)
    val (interactionTransitions, interactionValidationErrors) = actionDescriptors.map {
      _.toInteractionTransition(recipe.defaultFailureStrategy, ingredientExtractor)
    }.unzip

    // events provided from outside
    val sensoryEventTransitions: Seq[EventTransition[_]] = recipe.events.map { new EventTransition(_) }.toSeq

    // events provided by other transitions / actions
    val interactionEventTransitions: Seq[Transition[Unit, Unit, ProcessState]] = interactionTransitions.flatMap { t =>
      t.providesType match {
        case e: ProvidesEvent => {
          e.outputEventClasses.map(
          clazz => IntermediateTransition(id = clazz.getName.hashCode, label = clazz.getSimpleName))
        }
        case i: ProvidesIngredient => Nil
        case n: ProvidesNothing.type => Nil
      }
    }

    val allEventTransitions: Seq[Transition[_, _, _]] = sensoryEventTransitions ++ interactionEventTransitions

    // Given the event classes, it is creating the ingredient places and
    // connecting a transition to a ingredient place.
    val internalEventArcs: Seq[Arc] = interactionTransitions.flatMap { t =>
      t.providesType match {
        case e: ProvidesEvent => {
          e.outputEventClasses.flatMap(clazz =>
            clazz.getDeclaredFields.toSeq.map(field =>
              arc(interactionEventTransitions.getByLabel(clazz.getSimpleName), createPlace(field.getName, IngredientPlace), 1)))
        }
        case i: ProvidesIngredient => Nil
        case n: ProvidesNothing.type => Nil
      }
    }

    // This generates precondition arcs for Required Events (AND).
    val (eventPreconditionArcs, preconditionANDErrors) = actionDescriptors.map { t =>
      buildEventAndPreconditionArcs(t,
                                    allEventTransitions.findTransitionsByClass,
                                    interactionTransitions.findTransitionByName)
    }.unzipFlatten

    // This generates precondition arcs for Required Events (OR).
    val (eventOrPreconditionArcs, preconditionORErrors) = actionDescriptors.map { t =>
      buildEventORPreconditionArcs(t,
                                   allEventTransitions.findTransitionsByClass,
                                   interactionTransitions.findTransitionByName)
    }.unzipFlatten

    def providedIngredients[E](e: EventTransition[E]) = ingredientExtractor.extractIngredientTypes(e.clazz).keys.toSeq

    val (sensoryEventNoIngredients, sensoryEventWithIngredients) = sensoryEventTransitions.partition(sensoryEvent => providedIngredients(sensoryEvent).isEmpty)

    // It connects a sensory event to an ingredient places
    val sensoryEventArcs: Seq[Arc] = sensoryEventWithIngredients
      .flatMap(t => providedIngredients(t).map(fieldName => arc(t, createPlace(fieldName, IngredientPlace), 1)))

    val eventThatArePreconditions: Seq[String] =
      actionDescriptors.flatMap {
        actionDescriptor => actionDescriptor.requiredEvents.map(_.getSimpleName) ++ actionDescriptor.requiredOneOfEvents.map(_.getSimpleName)
      }

    // It connects a sensory event to a dummy ingredient so it can be modelled into the Petri net
    val sensoryEventArcsNoIngredientsArcs: Seq[Arc] = sensoryEventNoIngredients
      //Filter out events that are preconditions to interactions
      .filterNot(sensoryEvent => eventThatArePreconditions.contains(sensoryEvent.label))
      .map(sensoryEvent => arc(sensoryEvent, createPlace(sensoryEvent.label, EmptyEventIngredientPlace), 1))

    // First find the cases where multiple transitions depend on the same ingredient place
    val ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition[_]]] =
      getIngredientsWithMultipleConsumers(interactionTransitions)

    // Add one new transition for each duplicate input (the newly added one in the image above)
    val multipleConsumerFacilitatorTransitions: Seq[Transition[_, _, _]] =
      ingredientsWithMultipleConsumers.keys
        .map(name => MultiFacilitatorTransition(id = name.hashCode, label = name))
        .toSeq

    val multipleOutputFacilitatorArcs: Seq[Arc] =
      multipleConsumerFacilitatorTransitions.map(t =>
        arc(createPlace(t.label, IngredientPlace), t, 1))

    val interactionArcs: Seq[Arc] =
      interactionTransitions.flatMap(
        buildInteractionArcs(multipleConsumerFacilitatorTransitions,
                             ingredientsWithMultipleConsumers,
                             interactionEventTransitions.findTransitionsByClass))

    val petriNet: RecipePetriNet = createPetriNet[ProcessState](
      interactionArcs
        ++ eventPreconditionArcs
        ++ eventOrPreconditionArcs
        ++ sensoryEventArcs
        ++ sensoryEventArcsNoIngredientsArcs
        ++ internalEventArcs
        ++ multipleOutputFacilitatorArcs: _*)

    val initialMarking: Marking[Place] = interactionTransitions.flatMap { t =>
      t.maximumInteractionCount.map(n =>
        createPlace(s"limit:${t.label}", FiringLimiterPlace) -> Map(() -> n))
    }.toMarking

    val compiledRecipe = CompiledRecipe(
      name = recipe.name,
      petriNet = petriNet,
      initialMarking = initialMarking,
      sensoryEvents = recipe.events.asInstanceOf[Set[Class[_]]],
      ingredientExtractor,
      validationErrors = interactionValidationErrors.flatten ++ preconditionORErrors ++ preconditionANDErrors
    )

    RecipeValidations.postCompileValidations(compiledRecipe, validationSettings)
  }

  def compileRecipe(recipe: Recipe): CompiledRecipe =
    compileRecipe(recipe, ValidationSettings.defaultValidationSettings, defaultIngredientExtractor)

  private def getMultiTransition(internalRepresentationName: String,
                                 transitions: Seq[Transition[_, _, _]]): Transition[_, _, _] = {
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
      transition     <- actionTransitions
      inputPlaceName <- transition.requiredIngredientNames
    } yield (inputPlaceName, transition)

    // Then obtain the places with multiple out-adjacent transitions
    val ingredientsWithMultipleConsumers = placeNameWithTransition.groupBy {
      case (placeName, _) => placeName
    } // Group by place name
    .filter { case (_, interactions) => interactions.size >= 2 } // Only keep those place names which have more than one out-adjacent transition
    .map { case (placeName, interactions) => (placeName, interactions.map(_._2)) } // Cleanup the data structure

    ingredientsWithMultipleConsumers
  }

  private def createPlace(label: String, placeType: PlaceType): Place[Any] = Place(id = label.hashCode, label = label, placeType)
}
