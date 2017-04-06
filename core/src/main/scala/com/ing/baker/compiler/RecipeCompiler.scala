package com.ing.baker
package compiler

import com.ing.baker.compiler.transitions._
import com.ing.baker.core.{InteractionDescriptor, ProcessState}
import io.kagera.api._
import io.kagera.api.colored._
import io.kagera.api.colored.dsl._

import scala.language.postfixOps

object RecipeCompiler {

  implicit class TupleSeqOps[A, B](seq: Seq[(Seq[A], Seq[B])]) {
    def unzipFlatten: (Seq[A], Seq[B]) = seq.unzip match { case (a, b) => (a.flatten, b.flatten) }
  }

  /**
    * Creates a transition for a missing event in the recipe.
    */
  private def missingEventTransition(clazz: Class[_]): Transition[_, _, _] = {
    val label = s"$missingEvent ${clazz.getSimpleName}"
    nullTransition(label.hashCode, Some(label))
  }

  private def multipleConsumerFacilitatorTransition(label: String) =
    nullTransition(id = label.hashCode, label = Some(label), automated = true)

  private def buildEventAndPreconditionArcs(
      interaction: InteractionDescriptor[_],
      preconditionTransition: Class[_] => Option[Transition[_, _, _]],
      interactionTransition: String => Option[Transition[_, _, _]]): (Seq[Arc], Seq[String]) = {

    interaction.requiredEvents.toSeq.map { eventClass =>
      // a new `Place` generated for each AND events
      val eventPreconditionPlace =
        placeWithLabel(s"$preconditionPrefix${eventClass.getSimpleName}-${interaction.name}")
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
    val eventPreconditionPlace = placeWithLabel(s"$orPreconditionPrefix-${interaction.name}")

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

    val notProvidedError = (!eventTransition.isDefined).toOption {
      s"Event '$eventClass' for '${interactionTransition}' is not provided in the recipe"
    }.toSeq

    val arcs = Seq(
      arc(eventTransition.getOrElse(missingEventTransition(eventClass)), preconditionPlace, 1),
      arc(preconditionPlace, interactionTransition, 1)
    )

    (arcs, notProvidedError)
  }

  // the (possible) event output arcs / places
  private def interactionEventOutputArc(
      t: InteractionTransition[_],
      findInternalEventByClass: Class[_] => Option[Transition[_, _, _]]): Seq[Arc] = {
    val resultPlace = placeWithLabel(s"$interactionEvent${t.label}")
    val eventArcs = t.outputEventClasses.map { eventClass =>
      val internalEventTransition = findInternalEventByClass(eventClass).get
      val filter                  = (value: Any) => value == eventClass.getSimpleName

      arc(resultPlace, internalEventTransition, 1, filter)
    }
    arc(t, resultPlace, 1) +: eventArcs
  }

  // the (possible) data output arcs / places
  private def interactionIngredientOutputArc(t: InteractionTransition[_]): Seq[Arc] =
    t.outputFieldNames.map(placeWithLabel).map(p => arc(t, p, 1))

  private def buildInteractionInputArcs(
      t: InteractionTransition[_],
      multipleConsumerFacilitatorTransitions: Seq[Transition[_, _, _]],
      ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition[_]]]): Seq[Arc] = {

    val (fieldNamesWithPrefixMulti, fieldNamesWithoutPrefix) =
      t.requiredIngredientNames.toSeq.partition(ingredientsWithMultipleConsumers.contains)

    // the extra arcs to model multiple output transitions from one place
    val internalDataInputArcs = fieldNamesWithPrefixMulti flatMap { fieldName =>
      val multiTransitionPlace = placeWithLabel(s"$multiTransitionPrefix${t.label}-$fieldName")
      Seq(
          // one arc from multiplier place to the transition
          arc(getMultiTransition(s"$multiTransitionPrefix$fieldName",
                                 multipleConsumerFacilitatorTransitions),
              multiTransitionPlace,
              1),
          // one arc from extra added place to transition
          arc(multiTransitionPlace, t, 1))
    }

    // the data input arcs / places
    val dataInputArcs =
      fieldNamesWithoutPrefix.map(fieldName => arc(placeWithLabel(fieldName), t, 1))

    val limitInteractionCountArc =
      t.maximumInteractionCount.map(n => arc(placeWithLabel(s"$limitPrefix:${t.label}"), t, 1))

    dataInputArcs ++ internalDataInputArcs ++ limitInteractionCountArc
  }

  private def buildInteractionOutputArcs(
      t: InteractionTransition[_],
      findInternalEventByClass: Class[_] => Option[Transition[_, _, _]]): Seq[Arc] = {
    if (t.providesEvent)
      interactionEventOutputArc(t, findInternalEventByClass)
    else
      interactionIngredientOutputArc(t)
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

  private def buildSieveImplementationProviders(
      actions: Seq[InteractionDescriptor[_]]): (Map[Class[_], () => AnyRef], Seq[String]) = {

    val actionsMap: Map[Class[_], () => AnyRef] = actions
        .map(_.interactionClass)
        .map(clazz => clazz -> (() => clazz.newInstance().asInstanceOf[AnyRef]))
        .toMap

    val noDefaultConstructorErrors = actions
      .map(action => {
        if (action.interactionClass.getConstructors.exists(e => e.getParameterCount == 0)) ""
        else s"No default constructor found for Sieve: '${action.interactionClass}'"
      })
      .filter(_.nonEmpty)

    (actionsMap, noDefaultConstructorErrors)
  }

  val defaultIngredientExtractor: IngredientExtractor = new CompositeIngredientExtractor()

  /**
    * Compile the given recipe to a technical recipe that is useful for Baker.
    *
    * @param recipe; The Recipe to compile and execute
    * @param interactionImplementations: The implementations of the needed interactions
    * @param validationSettings The validation settings to follow for the validation
    * @return
    */
  def compileRecipe(recipe: Recipe,
                    interactionImplementations: Map[Class[_], () => AnyRef],
                    validationSettings: ValidationSettings,
                    ingredientExtractor: IngredientExtractor): CompiledRecipe = {

    val (sieveClassToImplementations, sieveErrors): (Map[Class[_], () => AnyRef], Seq[String]) =
      buildSieveImplementationProviders(recipe.sieveDescriptors)

    val actionDescriptors: Seq[InteractionDescriptor[_]] = recipe.interactionDescriptors ++ recipe.sieveDescriptors

    val allImplementations: Map[Class[_], () => AnyRef] =
      interactionImplementations ++ sieveClassToImplementations

    // For inputs for which no matching output cannot be found, we do not want to generate a place.
    // It should be provided at runtime from outside the active petri net (marking)
    val (interactionTransitions, interactionValidationErrors) = actionDescriptors.map {
      _.toInteractionTransition(allImplementations, recipe.defaultFailureStrategy, ingredientExtractor)
    }.unzip

    // events provided from outside
    val sensoryEventTransitions: Seq[EventTransition[_]] = recipe.events.map { new EventTransition(_, ingredientExtractor) }.toSeq

    // events provided by other transitions / actions
    val interactionEventTransitions = interactionTransitions.flatMap { t =>
      t.outputEventClasses.map(
        clazz =>
          nullTransition(id = clazz.getName.hashCode,
                         label = Some(clazz.getSimpleName),
                         automated = true))
    }

    val allEventTransitions: Seq[Transition[_, _, _]] = sensoryEventTransitions ++ interactionEventTransitions

    // Given the event classes, it is creating the ingredient places and
    // connecting a transition to a ingredient place.
    val internalEventArcs = interactionTransitions.flatMap { t =>
      t.outputEventClasses.flatMap(clazz =>
          clazz.getDeclaredFields.toSeq.map(field =>
              arc(interactionEventTransitions.getByLabel(clazz.getSimpleName), placeWithLabel(field.getName), 1)))
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

    // It connects a sensory event to an ingredient places
    val sensoryEventArcs: Seq[Arc] = sensoryEventTransitions
      //Filter out events that have no ingredients
      .filterNot(s => s.providedIngredients.isEmpty)
      .flatMap(t => t.providedIngredients.toSeq.map(fieldName => arc(t, placeWithLabel(fieldName), 1)))

    val eventThatArePreconditions: Seq[String] =
      actionDescriptors.flatMap {
        actionDescriptor => actionDescriptor.requiredEvents.map(_.getSimpleName) ++ actionDescriptor.requiredOneOfEvents.map(_.getSimpleName)
      }

    // It connects a sensory event to a dummy ingredient so it can be modelled into the Petri net
    val sensoryEventArcsNoIngredients: Seq[Arc] = sensoryEventTransitions
      //Filter out events that have ingredients
      .filter(sensoryEvent => sensoryEvent.providedIngredients.isEmpty)
      //Filter out events that are preconditions to interactions
      .filterNot(sensoryEvent => eventThatArePreconditions.contains(sensoryEvent.label))
      //TODO stop creating a Seq of 1 element. This is done because I could not find a better way.
      .flatMap(sensoryEvent => Seq(emptyEventIngredient + sensoryEvent.label).map(fieldName => arc(sensoryEvent, placeWithLabel(fieldName), 1)))

    // First find the cases where multiple transitions depend on the same ingredient place
    val ingredientsWithMultipleConsumers: Map[String, Seq[InteractionTransition[_]]] =
      getIngredientsWithMultipleConsumers(interactionTransitions)

    // Add one new transition for each duplicate input (the newly added one in the image above)
    val multipleConsumerFacilitatorTransitions: Seq[Transition[_, _, _]] =
      ingredientsWithMultipleConsumers.keys
        .map(name => multipleConsumerFacilitatorTransition(s"$multiTransitionPrefix$name"))
        .toSeq

    val multipleOutputFacilitatorArcs: Seq[Arc] =
      multipleConsumerFacilitatorTransitions.map(t =>
        arc(placeWithLabel(trimPrefix(t.label, multiTransitionPrefix)), t, 1))

    val interactionArcs: Seq[Arc] =
      interactionTransitions.flatMap(
        buildInteractionArcs(multipleConsumerFacilitatorTransitions,
                             ingredientsWithMultipleConsumers,
                             interactionEventTransitions.findTransitionsByClass))

    val petriNet: ExecutablePetriNet[ProcessState] = createPetriNet[ProcessState](
      interactionArcs
        ++ eventPreconditionArcs
        ++ eventOrPreconditionArcs
        ++ sensoryEventArcs
        ++ sensoryEventArcsNoIngredients
        ++ internalEventArcs
        ++ multipleOutputFacilitatorArcs: _*)

    val initialMarking: Marking = interactionTransitions.flatMap { t =>
      t.maximumInteractionCount.map(n =>
        placeWithLabel(s"$limitPrefix:${t.label}") -> Map(() -> n))
    }.toMarking

    val compiledRecipe = CompiledRecipe(
      name = recipe.name,
      petriNet = petriNet,
      initialMarking = initialMarking,
      sensoryEvents = recipe.events,
      ingredientExtractor,
      validationErrors = interactionValidationErrors.flatten ++ preconditionORErrors ++ preconditionANDErrors ++ sieveErrors
    )

    RecipeValidations.postCompileValidations(compiledRecipe, validationSettings)
  }

  def compileRecipe(recipe: Recipe): CompiledRecipe =
    compileRecipe(recipe, Map.empty, ValidationSettings.defaultValidationSettings, defaultIngredientExtractor)

  def compileRecipe(recipe: Recipe, validationSettings: ValidationSettings): CompiledRecipe =
    compileRecipe(recipe, Map.empty, validationSettings, defaultIngredientExtractor)

  // transform multi:dossierId ---> dossierId
  private def trimPrefix(label: String, prefix: String) = label.replace(prefix, "")

  private def getMultiTransition(internalRepresentationName: String,
                                 transitions: Seq[Transition[_, _, _]]): Transition[_, _, _] = {
    transitions
      .find(t => t.label.contains(internalRepresentationName))
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

  private def placeWithLabel(label: String) = Place[Any](id = label.hashCode, label = Some(label))
}
