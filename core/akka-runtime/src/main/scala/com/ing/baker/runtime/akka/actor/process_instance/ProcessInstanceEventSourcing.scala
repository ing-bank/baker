package com.ing.baker.runtime.akka.actor.process_instance

import akka.NotUsed
import akka.actor.{ActorSystem, NoSerializationVerificationNeeded}
import akka.persistence.query.scaladsl.CurrentEventsByPersistenceIdQuery
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.sensors.actor.PersistentActorMetrics
import akka.stream.scaladsl.Source
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.Event
import com.ing.baker.runtime.akka.actor.process_instance.internal.{ExceptionState, ExceptionStrategy, Instance, Job}
import com.ing.baker.runtime.akka.actor.serialization.AkkaSerializerProvider
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetaDataName
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
    * An event describing the fact that a transition has been postponed to be fired.
    */
  case class TransitionDelayed(override val jobId: Long,
                               override val transitionId: Id,
                               consumed: Marking[Id]) extends TransitionEvent

  /**
    * An event describing the fact that a transition has been postponed to be fired.
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

  def apply[P : Identifiable, T : Identifiable, S, E](sourceFn: T => (S => E => S)): Instance[P, T, S] => Event => Instance[P, T, S] = instance => {
    case InitializedEvent(initial, initialState) =>

      val initialMarking: Marking[P] = initial.unmarshall(instance.petriNet.places)

      Instance[P, T, S](instance.petriNet, 1, initialMarking, Map.empty, initialState.asInstanceOf[S], Map.empty, Set.empty)
    case e: TransitionFiredEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])
      val consumed: Marking[P] = e.consumed.unmarshall(instance.petriNet.places)
      val produced: Marking[P] = e.produced.unmarshall(instance.petriNet.places)

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed) |+| produced,
        receivedCorrelationIds = instance.receivedCorrelationIds ++ e.correlationId,
        state = newState,
        jobs = instance.jobs - e.jobId
      )
    case e: TransitionFailedEvent =>
      val transition = instance.petriNet.transitions.getById(e.transitionId)

      val consumed: Marking[P] = e.consume.unmarshall(instance.petriNet.places)

      val job = instance.jobs.getOrElse(e.jobId, {
        Job[P, T, S](e.jobId, e.correlationId, instance.state, transition, consumed, e.input, None)
      })
      val failureCount = job.failureCount + 1
      val updatedJob: Job[P, T, S] = job.copy(failure = Some(ExceptionState(e.timeFailed, failureCount, e.failureReason, e.exceptionStrategy)))
      instance.copy[P, T, S](jobs = instance.jobs + (job.id -> updatedJob))

    case e: TransitionDelayed =>
      val consumed: Marking[P] = e.consumed.unmarshall(instance.petriNet.places)

      val delayedInstanceCount: Int = instance.delayedTransitionIds.getOrElse(e.transitionId, 0)

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = (instance.marking |-| consumed),
        delayedTransitionIds = instance.delayedTransitionIds + (e.transitionId -> (delayedInstanceCount + 1)), //Claim the consumed tokens
        jobs = instance.jobs - e.jobId
      )

    case e: DelayedTransitionFired =>
      val delayedInstanceCount: Int = instance.delayedTransitionIds(e.transitionId)
      val produced: Marking[P] = e.produced.unmarshall(instance.petriNet.places)
      val transition = instance.petriNet.transitions.getById(e.transitionId)
      val newState = sourceFn(transition)(instance.state)(e.output.asInstanceOf[E])

      instance.copy[P, T, S](
        sequenceNr = instance.sequenceNr + 1,
        marking = instance.marking |+| produced,
        delayedTransitionIds = instance.delayedTransitionIds + (e.transitionId -> (delayedInstanceCount - 1)),
        state = newState
      )

    case e: MetaDataAdded =>
        val newState: S = instance.state match {
          case state: RecipeInstanceState =>
            val newBakerMetaData: Map[String, String] =
              state.ingredients.get(RecipeInstanceMetaDataName) match {
                case Some(value) =>
                  if(value.isInstanceOf(MapType(CharArray))) {
                    val oldMetaData: Map[String, String] = value.asMap[String, String](classOf[String], classOf[String]).asScala.toMap
                    oldMetaData ++ e.metaData
                  }
                  else {
                    //If the old metadata is not of Type[String, String] we overwrite it since this is not allowed.
                    logger.info("Old RecipeInstanceMetaData was not of type Map[String, String]")
                    e.metaData
                  }
                case None =>
                  e.metaData
              }
            val newIngredients: Map[String, Value] =
              state.ingredients + (RecipeInstanceMetaDataName -> com.ing.baker.types.Converters.toValue(newBakerMetaData))
            state.copy(ingredients = newIngredients).asInstanceOf[S]
          case state =>
            state
      }
      instance.copy[P, T, S](state = newState)
  }

  def eventsForInstance[P : Identifiable, T : Identifiable, S, E](
      processTypeName: String,
      recipeInstanceId: String,
      topology: PetriNet[P, T],
      encryption: Encryption,
      readJournal: CurrentEventsByPersistenceIdQuery,
      eventSourceFn: T => (S => E => S))(implicit actorSystem: ActorSystem): Source[(Instance[P, T, S], Event), NotUsed] = {

    val serializer = new ProcessInstanceSerialization[P, T, S, E](AkkaSerializerProvider(actorSystem, encryption))

    val persistentId = ProcessInstance.recipeInstanceId2PersistenceId(processTypeName, recipeInstanceId)
    val src = readJournal.currentEventsByPersistenceId(persistentId, 0, Long.MaxValue)
    val eventSource = ProcessInstanceEventSourcing.apply[P, T, S, E](eventSourceFn)

    // TODO: remove null value
    src.scan[(Instance[P, T, S], Event)]((Instance.uninitialized[P, T, S](topology), null.asInstanceOf[Event])) {
      case ((instance, _), e) =>
        val serializedEvent = e.event.asInstanceOf[AnyRef]
        val deserializedEvent = serializer.deserializeEvent(serializedEvent)(instance)
        val updatedInstance = eventSource.apply(instance)(deserializedEvent)
        (updatedInstance, deserializedEvent)
    }.drop(1) // Just to drop the first event 'uninitialized', not interesting for the consumers.
  }
}

abstract class ProcessInstanceEventSourcing[P : Identifiable, T : Identifiable, S, E](
    val petriNet: PetriNet[P, T],
    encryption: Encryption,
    eventSourceFn: T => (S => E => S)) extends PersistentActor with PersistentActorMetrics {

  protected implicit val system: ActorSystem = context.system

  protected val eventSource: Instance[P, T, S] => Event => Instance[P, T, S] =
    ProcessInstanceEventSourcing.apply[P, T, S, E](eventSourceFn)

  private val serializer = new ProcessInstanceSerialization[P, T, S, E](AkkaSerializerProvider(system, encryption))

  def onRecoveryCompleted(state: Instance[P, T, S]): Unit

  def persistEvent[O](instance: Instance[P, T, S], e: Event)(fn: Event => O): Unit = {
    val serializedEvent = serializer.serializeEvent(e)(instance)
    persist(serializedEvent) { persisted => fn(e) }
  }

  private var recoveringState: Instance[P, T, S] = Instance.uninitialized[P, T, S](petriNet)

  private def applyToRecoveringState(e: AnyRef): Unit = {
    val deserializedEvent = serializer.deserializeEvent(e)(recoveringState)
    recoveringState = eventSource(recoveringState)(deserializedEvent)
  }

  override def receiveRecover: Receive = {
    case e: protobuf.Initialized      => applyToRecoveringState(e)
    case e: protobuf.TransitionFired  => applyToRecoveringState(e)
    case e: protobuf.TransitionFailed => applyToRecoveringState(e)
    case e: protobuf.TransitionDelayed => applyToRecoveringState(e)
    case e: protobuf.DelayedTransitionFired => applyToRecoveringState(e)
    case e: protobuf.MetaDataAdded => applyToRecoveringState(e)
    case RecoveryCompleted =>
      if (recoveringState.sequenceNr > 0)
        onRecoveryCompleted(recoveringState)
  }
}
