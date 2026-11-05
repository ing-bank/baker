package com.ing.baker.runtime.akka.actor.process_instance

import com.ing.baker.il.petrinet.{EventTransition, Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.internal.{ExceptionState, ExceptionStrategy, Instance, Job}
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import com.ing.baker.types.Value
import com.typesafe.scalalogging.LazyLogging

object ProcessInstanceEventSourcing extends LazyLogging {

  sealed trait Event

  sealed trait TransitionEvent extends Event {
    val jobId: Long
    val transitionId: Id
  }

  /**
   * An event describing the fact that a transition has fired in the petri net process.
   */
  case class TransitionFiredEvent(override val jobId: Long,
                                  override val transitionId: Id,
                                  correlationId: Option[String],
                                  timeStarted: Long,
                                  timeCompleted: Long,
                                  consumed: Marking[Id],
                                  produced: Marking[Id],
                                  output: Any) extends TransitionEvent

  /**
   * An event describing the fact that a transition failed but was continued with a given event
   * This does not consume the input and puts the transition in a blocked state but does create the output.
   */
  case class TransitionFailedWithOutputEvent(override val jobId: Long,
                                             override val transitionId: Id,
                                             correlationId: Option[String],
                                             timeStarted: Long,
                                             timeCompleted: Long,
                                             consumed: Marking[Id],
                                             produced: Marking[Id],
                                             output: Any) extends TransitionEvent


  /**
   * An event describing the fact that a transition failed but was continued with a given event
   * This does not consume the input and puts the transition in a blocked state but does create the output.
   */
  case class TransitionFailedWithFunctionalOutputEvent(override val jobId: Long,
                                                       override val transitionId: Id,
                                                       correlationId: Option[String],
                                                       timeStarted: Long,
                                                       timeCompleted: Long,
                                                       consumed: Marking[Id],
                                                       produced: Marking[Id],
                                                       output: Any) extends TransitionEvent

  /**
   * An event describing the fact that a transition failed to fire.
   */
  case class TransitionFailedEvent(override val jobId: Long,
                                   override val transitionId: Id,
                                   correlationId: Option[String],
                                   timeStarted: Long,
                                   timeFailed: Long,
                                   consume: Marking[Id],
                                   input: Any,
                                   failureReason: String,
                                   exceptionStrategy: ExceptionStrategy) extends TransitionEvent

  /**
   * An event describing the fact that a transition has been delayed.
   */
  case class TransitionDelayed(override val jobId: Long,
                               override val transitionId: Id,
                               consumed: Marking[Id]) extends TransitionEvent

  /**
   * An event describing the fact that a transition has been fired after its delay.
   */
  case class DelayedTransitionFired(override val jobId: Long,
                                    override val transitionId: Id,
                                    timeCompleted: Long,
                                    produced: Marking[Id],
                                    output: Any) extends TransitionEvent

  /**
   * An event describing the fact that an instance was initialized.
   */
  case class InitializedEvent(marking: Marking[Id],
                              state: Any) extends Event

  /**
   * An event that describes the metaData being updated
   * @param metaData
   */
  case class MetaDataAdded(metaData: Map[String, String]) extends Event

  /**
   * An event that describes a listener being added for process completion.
   * @param listenerPath The serialized path of the listener actor.
   */
  case class CompletionListenerAdded(listenerPath: String) extends Event

  /**
   * An event that describes a listener being added for a specific event occurrence.
   * @param eventName The name of the event to listen for.
   * @param listenerPath The serialized path of the listener actor.
   */
  case class EventListenerAdded(eventName: String, listenerPath: String) extends Event

  /**
   * An event that signifies that all completion listeners have been notified and should be removed.
   */
  case class CompletionListenersRemoved() extends Event

  /**
   * An event that signifies that all listeners for a specific event have been notified and should be removed.
   * @param eventName The event for which listeners are removed.
   */
  case class EventListenersRemoved(eventName: String) extends Event

  def apply[S, E](sourceFn: (Long, Transition) => (S => E => S)): Instance[S] => Event => Instance[S] = instance => {
    case InitializedEvent(initial, initialState) =>

      val initialMarking: Marking[Place] = initial.unmarshall(instance.petriNet.places)

      Instance[S](instance.petriNet, 1, initialMarking, Map.empty, initialState.asInstanceOf[S], Map.empty, Set.empty)

    case e: TransitionFiredEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      // Decrement counter for event transitions (with safeguard to prevent negative)
      val isEventTransition = transition.isInstanceOf[EventTransition]
      val updatedCounter = if (isEventTransition)
        math.max(0, instance.inFlightEventTransitions - 1)
      else
        instance.inFlightEventTransitions

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId,
        inFlightEventTransitions = updatedCounter
      )

    case e: TransitionFailedWithOutputEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[S](e.jobId, e.correlationId, instance.state, transition, consumed, null, None)
      })
      val updatedJob: Job[S] = job.copy(failure = Some(ExceptionState(0, 1, "Blocked after FireEvent retry strategy", ExceptionStrategy.BlockTransition)))

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = instance.marking |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs + (job.id -> updatedJob)
      )

    case e: TransitionFailedWithFunctionalOutputEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      // Decrement counter for event transitions (with safeguard to prevent negative)
      val isEventTransition = transition.isInstanceOf[EventTransition]
      val updatedCounter = if (isEventTransition)
        math.max(0, instance.inFlightEventTransitions - 1)
      else
        instance.inFlightEventTransitions

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId,
        inFlightEventTransitions = updatedCounter
      )

    case e: TransitionFailedEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)

      val consumed: Marking[Place] = e.consume.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[S](e.jobId, e.correlationId, instance.state, transition, consumed, e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))

      // Decrement counter for event transitions that are NOT retrying
      // Retrying transitions are still "in-flight" so counter should remain
      val isEventTransition = transition.isInstanceOf[EventTransition]
      val isRetrying = e.exceptionStrategy.isInstanceOf[ExceptionStrategy.RetryWithDelay]
      val updatedCounter = if (isEventTransition && !isRetrying)
        math.max(0, instance.inFlightEventTransitions - 1)
      else
        instance.inFlightEventTransitions

      instance.copy[S](
        jobs = instance.jobs + (job.id -> updatedJob),
        inFlightEventTransitions = updatedCounter
      )

    case e: TransitionDelayed =>
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)

      val delayedInstanceCount: Int = instance.delayedTransitionIds.getOrElse(e.transitionId, 0)

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed),
        delayedTransitionIds = instance.delayedTransitionIds + (e.transitionId -> (delayedInstanceCount + 1)), //Claim the consumed tokens
        jobs = instance.jobs - e.jobId
      )

    case e: DelayedTransitionFired =>
      val delayedInstanceCount: Int = instance.delayedTransitionIds(e.transitionId)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(e.timeCompleted, transition)(instance.state)(e.output.asInstanceOf[E])

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = instance.marking |+| produced,
        delayedTransitionIds = instance.delayedTransitionIds + (e.transitionId -> (delayedInstanceCount - 1)),
        state = newState
      )

    case e: MetaDataAdded =>
      val newState: S = instance.state match {
        case state: RecipeInstanceState =>
          val newRecipeInstanceMetaData: Map[String, String] = state.recipeInstanceMetadata ++ e.metaData
          //We still add an ingredient for the metaData since this makes it easier to use it during interaction execution
          val newIngredients: Map[String, Value] = state.ingredients +
            (RecipeInstanceMetadataName -> com.ing.baker.types.Converters.toValue(newRecipeInstanceMetaData))
          state.copy(ingredients = newIngredients, recipeInstanceMetadata = newRecipeInstanceMetaData).asInstanceOf[S]
        case state =>
          state
      }
      instance.copy[S](state = newState)

    case e: CompletionListenerAdded =>
      instance.copy(
        completionListenerPaths = instance.completionListenerPaths + e.listenerPath
      )

    case e: EventListenerAdded =>
      val currentListeners = instance.eventListenerPaths.getOrElse(e.eventName, Set.empty)
      val updatedListeners = currentListeners + e.listenerPath
      instance.copy(
        eventListenerPaths = instance.eventListenerPaths + (e.eventName -> updatedListeners)
      )

    case _: CompletionListenersRemoved =>
      instance.copy(
        completionListenerPaths = Set.empty
      )

    case e: EventListenersRemoved =>
      instance.copy(
        eventListenerPaths = instance.eventListenerPaths - e.eventName
      )
  }
}
