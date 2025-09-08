package com.ing.baker.runtime.model.recipeinstance

import cats.effect.concurrent.Deferred
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet.Place.IngredientPlace
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.common.IngredientInstance
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment}
import com.ing.baker.types.{CharArray, MapType, Value}

object RecipeInstanceState {

  def getMetaDataFromIngredients(ingredients: Map[String, Value]): Option[Map[String, String]] = {
    ingredients.get(RecipeInstanceMetadataName).flatMap(value => {
      if (value.isInstanceOf(MapType(CharArray)))
        Some(value.as[Map[String, String]])
      else
        Option.empty
    })
  }

  def getMetaDataFromIngredients(ingredients: Seq[IngredientInstance]): Option[Map[String, String]] =
    getMetaDataFromIngredients(ingredients.map(i => i.name -> i.value).toMap)

  def empty[F[_]](recipeInstanceId: String, recipe: CompiledRecipe, createdOn: Long): RecipeInstanceState[F] =
    RecipeInstanceState(
      recipeInstanceId,
      recipe,
      createdOn,
      sequenceNumber = 0,
      marking = recipe.initialMarking,
      ingredients = Map.empty,
      recipeInstanceMetadata = Map.empty,
      events = List.empty,
      completedCorrelationIds = Set.empty,
      executions = Map.empty,
      retryingExecutions = Set.empty,
      idleListeners = Set.empty[Deferred[F, Unit]],
      eventListeners = Map.empty[String, Set[Deferred[F, Unit]]]
    )
}

case class RecipeInstanceState[F[_]](
                                      recipeInstanceId: String,
                                      recipe: CompiledRecipe,
                                      createdOn: Long,
                                      sequenceNumber: Long,
                                      marking: Marking[Place],
                                      ingredients: Map[String, Value],
                                      recipeInstanceMetadata: Map[String, String],
                                      events: List[EventMoment],
                                      completedCorrelationIds: Set[String],
                                      executions: Map[Long, TransitionExecution],
                                      retryingExecutions: Set[Long],
                                      idleListeners: Set[Deferred[F, Unit]] = Set.empty[Deferred[F, Unit]],
                                      eventListeners: Map[String, Set[Deferred[F, Unit]]] = Map.empty[String, Set[Deferred[F, Unit]]]
                                    ) extends RecipeInstanceEventValidation[F] {

  def isInactive: Boolean =
    executions.values.forall(_.isInactive)

  def addIdleListener(listener: Deferred[F, Unit]): RecipeInstanceState[F] =
    this.copy(idleListeners = idleListeners + listener)

  def addEventListener(eventName: String, listener: Deferred[F, Unit]): RecipeInstanceState[F] = {
    val currentListeners = eventListeners.getOrElse(eventName, Set.empty)
    this.copy(eventListeners = eventListeners + (eventName -> (currentListeners + listener)))
  }

  def getInteractionExecution(interactionName: String): Option[TransitionExecution] =
    for {
      transition <- recipe.interactionTransitions.find(_.interactionName == interactionName)
      transitionExecution <- executions.collectFirst {
        case (_, execution) if execution.transition.id == transition.id => execution }
    } yield transitionExecution

  def addExecution(execution: TransitionExecution*): RecipeInstanceState[F] =
    copy(executions = executions ++ execution.map(ex => ex.id -> ex))

  private def removeExecution(transitionExecution: TransitionExecution): RecipeInstanceState[F] =
    copy(executions = executions - transitionExecution.id)

  def recordFailedExecution(transitionExecution: TransitionExecution, exceptionStrategy: ExceptionStrategyOutcome): RecipeInstanceState[F] =
    addExecution(transitionExecution.toFailedState(exceptionStrategy))

  def recordFailedWithOutputExecution(transitionExecution: TransitionExecution, output: EventInstance): (RecipeInstanceState[F], Set[TransitionExecution]) =
    aggregateOutputEvent(Some(output))
      .increaseSequenceNumber
      .aggregatePetriNetChanges(transitionExecution, Some(output))
      .addCompletedCorrelationId(transitionExecution)
      .addExecution(transitionExecution.copy(state = TransitionExecution.State.Failed(transitionExecution.failureCount, ExceptionStrategyOutcome.BlockTransition)))
      .allEnabledExecutions

  def recordFailedWithOutputExecutionAsFunctionalEvent(transitionExecution: TransitionExecution, output: EventInstance): (RecipeInstanceState[F], Set[TransitionExecution]) =
    aggregateOutputEvent(Some(output))
      .increaseSequenceNumber
      .aggregatePetriNetChanges(transitionExecution, Some(output))
      .addCompletedCorrelationId(transitionExecution)
      .removeExecution(transitionExecution)
      .allEnabledExecutions

  def recordCompletedExecution(transitionExecution: TransitionExecution, output: Option[EventInstance]): (RecipeInstanceState[F], Set[TransitionExecution]) =
    aggregateOutputEvent(output)
      .increaseSequenceNumber
      .aggregatePetriNetChanges(transitionExecution, output)
      .addCompletedCorrelationId(transitionExecution)
      .removeExecution(transitionExecution)
      .allEnabledExecutions

  def addRetryingExecution(transitionExecutionId: Long): RecipeInstanceState[F] =
    copy(retryingExecutions = retryingExecutions + transitionExecutionId)

  def removeRetryingExecution(transitionExecutionId: Long): RecipeInstanceState[F] =
    copy(retryingExecutions = retryingExecutions - transitionExecutionId)

  private def allEnabledExecutions: (RecipeInstanceState[F], Set[TransitionExecution]) = {

    def canBeFiredAutomatically(transition: Transition): Boolean =
      transition match {
        case EventTransition(_, isSensoryEvent, _) => !isSensoryEvent
        case _ => true
      }

    val enabled  = enabledParameters(availableMarkings)
    val canFire = enabled.filter { case (transition, _) =>
      !hasFailed(transition) && canBeFiredAutomatically(transition)
    }
    val executions = canFire.map {
      case (transition: InteractionTransition, markings) =>
        TransitionExecution(
          recipeInstanceId = recipeInstanceId,
          recipe = recipe,
          transition = transition,
          consume = markings.head,
          input = None,
          ingredients = ingredients,
          recipeInstanceMetadata = recipeInstanceMetadata,
          eventList = events,
          correlationId = None,
          isReprovider = transition.isReprovider
        )
      case (transition, markings) =>
        TransitionExecution(
          recipeInstanceId = recipeInstanceId,
          recipe = recipe,
          transition = transition,
          consume = markings.head,
          input = None,
          ingredients = ingredients,
          recipeInstanceMetadata = recipeInstanceMetadata,
          eventList = events,
          correlationId = None,
          isReprovider =  false
        )
    }.toSeq

    addExecution(executions: _*) -> executions.toSet
  }

  private def aggregateOutputEvent(output: Option[EventInstance]): RecipeInstanceState[F] =
    output match {
      case None => this
      case Some(outputEvent) =>
        copy(
          ingredients = ingredients ++ outputEvent.providedIngredients,
          events = events :+ EventMoment(outputEvent.name, System.currentTimeMillis()))
    }

  private def increaseSequenceNumber: RecipeInstanceState[F] =
    copy(sequenceNumber = sequenceNumber + 1)

  private def aggregatePetriNetChanges(transitionExecution: TransitionExecution, output: Option[EventInstance]): RecipeInstanceState[F] = {
    val outputMarkings: MultiSet[Place] = recipe.petriNet.outMarking(transitionExecution.transition)

    val producedMarking: Marking[Place] = {
      outputMarkings.keys.map { place: Place =>
        val value: Any = output.map(_.name).orNull
        place -> MultiSet.copyOff(Seq(value))
      }.toMarking
    }

    val reproviderMarkings: Marking[Place] = if (transitionExecution.isReprovider) {
      outputMarkings.toMarking.filter((input: (Place, MultiSet[Any])) => input._1.placeType == IngredientPlace)
    } else Map.empty

    copy(marking = (marking |-| transitionExecution.consume) |+| producedMarking |+| reproviderMarkings)
  }

  private def addCompletedCorrelationId(transitionExecution: TransitionExecution): RecipeInstanceState[F] =
    copy(completedCorrelationIds = completedCorrelationIds ++ transitionExecution.correlationId)

  protected def availableMarkings: Marking[Place] = {
    val reservedMarkings =
      executions
        .map { case (_, execution) => execution.consume }
        .reduceOption(_ |+| _)
        .getOrElse(Marking.empty)
    marking |-| reservedMarkings
  }

  protected def hasFailed(transition: Transition): Boolean =
    executions.values
      .exists(t => t.transition.id == transition.id && t.isBlocked || t.isRetrying)

  protected def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] = {

    def consumableMarkings(transition: Transition): Iterable[Marking[Place]] = {
      // TODO this is not the most efficient, should break early when consumable tokens < edge weight
      val consumable = recipe.petriNet.inMarking(transition).map {
        case (place, count) =>
          val edge = recipe.petriNet.findPTEdge(place, transition).map(_.asInstanceOf[Edge]).get
          val consumableTokens = ofMarking.get(place) match {
            case None =>
              MultiSet.empty
            case Some(tokens) =>
              tokens.filter { case (e, _) => edge.isAllowed(e) }
          }
          (place, count, consumableTokens)
      }
      // check if any any places have an insufficient number of tokens
      if (consumable.exists { case (_, count, tokens) => tokens.multisetSize < count })
        Seq.empty
      else {
        val consume = consumable.map {
          case (place, count, tokens) => place -> MultiSet.copyOff[Any](tokens.allElements.take(count))
        }.toMarking
        // TODO lazily compute all permutations instead of only providing the first result
        Seq(consume)
      }
    }

    recipe.petriNet.transitions
      .filter(consumableMarkings(_).nonEmpty)
      .map(transition => transition -> consumableMarkings(transition)).toMap
  }
}