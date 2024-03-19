package com.ing.baker.runtime.akka.actor.process_instance

import akka.NotUsed
import akka.actor.{ActorSystem, NoSerializationVerificationNeeded}
import akka.persistence.query.scaladsl.CurrentEventsByPersistenceIdQuery
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.sensors.actor.PersistentActorMetrics
import akka.stream.scaladsl.Source
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.Event
import com.ing.baker.runtime.akka.actor.process_instance.internal.{ExceptionState, ExceptionStrategy, Instance, Job}
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetadataName
import com.ing.baker.runtime.scaladsl.RecipeInstanceState
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types.{CharArray, MapType, Value}
import com.typesafe.scalalogging.LazyLogging

import scala.jdk.CollectionConverters._

object ProcessInstanceEventSourcing extends LazyLogging {

  sealed trait Event extends NoSerializationVerificationNeeded

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

  def apply[S, E](sourceFn: Transition => (S => E => S)): Instance[S] => Event => Instance[S] = instance => {
    case InitializedEvent(initial, initialState) =>

      val initialMarking: Marking[Place] = initial.unmarshall(instance.petriNet.places)

      Instance[S](instance.petriNet, 1, initialMarking, Map.empty, initialState.asInstanceOf[S], Map.empty, Set.empty)

    case e: TransitionFiredEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[Place] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[Place] = e.produced.unmarshall(instance.petriNet.places)

      instance.copy[S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )

    case e: TransitionFailedWithOutputEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])
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

    case e: TransitionFailedEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)

      val consumed: Marking[Place] = e.consume.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[S](e.jobId, e.correlationId, instance.state, transition, consumed, e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[S](jobs = instance.jobs + (job.id -> updatedJob))

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
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])

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
  }

  def eventsForInstance[S, E](
      processTypeName: String,
      recipeInstanceId: String,
      topology: PetriNet,
      encryption: Encryption,
      readJournal: CurrentEventsByPersistenceIdQuery,
      eventSourceFn: Transition => (S => E => S))(implicit actorSystem: ActorSystem): Source[(Instance[S], Event), NotUsed] = {

    val serializer = new ProcessInstanceSerialization[S, E](AkkaSerializerProvider(actorSystem, encryption))

    val persistentId = ProcessInstance.recipeInstanceId2PersistenceId(processTypeName, recipeInstanceId)
    val src = readJournal.currentEventsByPersistenceId(persistentId, 0, Long.MaxValue)
    val eventSource = ProcessInstanceEventSourcing.apply[S, E](eventSourceFn)

    // TODO: remove null value
    src.scan[(Instance[S], Event)]((Instance.uninitialized[S](topology), null.asInstanceOf[Event])) {
      case ((instance, _), e) =>
        val serializedEvent = e.event.asInstanceOf[AnyRef]
        val deserializedEvent = serializer.deserializeEvent(serializedEvent)(instance)
        val updatedInstance = eventSource.apply(instance)(deserializedEvent)
        (updatedInstance, deserializedEvent)
    }.drop(1) // Just to drop the first event 'uninitialized', not interesting for the consumers.
  }
}

abstract class ProcessInstanceEventSourcing[S, E](
    val petriNet: PetriNet,
    encryption: Encryption,
    eventSourceFn: Transition => (S => E => S)) extends PersistentActor with PersistentActorMetrics {

  protected implicit val system: ActorSystem = context.system

  protected val eventSource: Instance[S] => Event => Instance[S] =
    ProcessInstanceEventSourcing.apply[S, E](eventSourceFn)

  private val serializer = new ProcessInstanceSerialization[S, E](AkkaSerializerProvider(system, encryption))

  def onRecoveryCompleted(state: Instance[S]): Unit

  def persistEvent[O](instance: Instance[S], e: Event)(fn: Event => O): Unit = {
    val serializedEvent = serializer.serializeEvent(e)(instance)
    persist(serializedEvent) { persisted => fn(e) }
  }

  private var recoveringState: Instance[S] = Instance.uninitialized[S](petriNet)

  private def applyToRecoveringState(e: AnyRef): Unit = {
    val deserializedEvent = serializer.deserializeEvent(e)(recoveringState)
    recoveringState = eventSource(recoveringState)(deserializedEvent)
  }

  override def receiveRecover: Receive = {
    case e: protobuf.Initialized      => applyToRecoveringState(e)
    case e: protobuf.TransitionFired  => applyToRecoveringState(e)
    case e: protobuf.TransitionFailedWithOutput  => applyToRecoveringState(e)
    case e: protobuf.TransitionFailed => applyToRecoveringState(e)
    case e: protobuf.TransitionDelayed => applyToRecoveringState(e)
    case e: protobuf.DelayedTransitionFired => applyToRecoveringState(e)
    case e: protobuf.MetaDataAdded => applyToRecoveringState(e)
    case RecoveryCompleted =>
      if (recoveringState.sequenceNr > 0)
        onRecoveryCompleted(recoveringState)
  }
}
