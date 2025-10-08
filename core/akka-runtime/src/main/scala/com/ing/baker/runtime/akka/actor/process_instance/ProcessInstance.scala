package com.ing.baker.runtime.akka.actor.process_instance

import akka.actor._
import akka.cluster.sharding.ShardRegion.Passivate
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.persistence.{DeleteMessagesFailure, DeleteMessagesSuccess}
import cats.effect.IO
import cats.effect.unsafe.IORuntime
import com.ing.baker.il.failurestrategy.{BlockInteraction, FireEventAfterFailure, FireFunctionalEventAfterFailure, RetryWithIncrementalBackoff}
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, Place}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor, checkpointEventInteractionPrefix}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActorProtocol.{FireDelayedTransitionAck, ScheduleDelayedTransition}
import com.ing.baker.runtime.akka.actor.logging.LogAndSendEvent
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventRejection
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstance._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceLogger._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.internal.ExceptionStrategy.{Continue, ContinueAsFunctionalEvent, RetryWithDelay}
import com.ing.baker.runtime.akka.actor.process_instance.internal._
import com.ing.baker.runtime.akka.actor.process_instance.{ProcessInstanceProtocol => protocol}
import com.ing.baker.runtime.akka.internal.{FatalInteractionException, RecipeRuntime}
import com.ing.baker.runtime.model.BakerLogging
import com.ing.baker.runtime.scaladsl.{EventFired, EventInstance, EventReceived, EventRejected, IngredientInstance, RecipeInstanceState}
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types.{FromValue, PrimitiveValue, Value}

import scala.collection.{immutable, mutable}
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import scala.language.existentials
import scala.util.Try

object ProcessInstance {

  case class Settings(executionContext: ExecutionContext,
                      ioRuntime: IORuntime,
                      idleTTL: Option[FiniteDuration],
                      encryption: Encryption,
                      getIngredientsFilter: Seq[String],
                      providedIngredientFilter: Seq[String])

  case class IdleStop(seq: Long) extends NoSerializationVerificationNeeded

  def persistenceIdPrefix(processType: String) = s"process-$processType-"

  def recipeInstanceId2PersistenceId(processType: String, recipeInstanceId: String): String = persistenceIdPrefix(processType) + recipeInstanceId

  def persistenceId2recipeInstanceId(processType: String, persistenceId: String): Option[String] = {
    val parts = persistenceId.split(persistenceIdPrefix(processType))
    if (parts.length == 2)
      Some(parts(1))
    else
      None
  }

  def props[S, E](processType: String, compiledRecipe: CompiledRecipe,
                  runtime: ProcessInstanceRuntime,
                  settings: Settings,
                  delayedTransitionActor: ActorRef): Props =
    Props(new ProcessInstance(
      processType,
      compiledRecipe,
      settings,
      runtime,
      delayedTransitionActor)
    )

  private def filterIngredients(ingredients: Map[String, Value], ingredientFilter: Seq[String]) = {
    val filterAll: Boolean = ingredientFilter.contains("*")
    ingredients.map {
      ingredient =>
        if (filterAll || ingredientFilter.contains(ingredient._1))
          ingredient._1 -> PrimitiveValue("")
        else
          ingredient
    }
  }

  def getOutputEventName(interactionTransition: InteractionTransition,
                         log: DiagnosticLoggingAdapter): String = {
    def getOutputEventNameWithRetryStrategyFiltered(fireEvent: EventDescriptor, eventsToFire: Seq[EventDescriptor]): String = {
      val outputEventsNames: Seq[String] = eventsToFire.map(_.name)
      if (outputEventsNames.size != 2)
        throw new FatalInteractionException(s"Delayed transitions must have 2 input ingredients if FireEventAfterFailure strategy is used")
      outputEventsNames.filter(_ != fireEvent.name).head
    }

    def getFirstOutputEventName(eventsToFire: Seq[EventDescriptor]): String = {
      val outputEvents = interactionTransition.eventsToFire
      if (outputEvents.size != 1)
        throw new FatalInteractionException(s"Delayed transitions can only have 1 input ingredient")
      outputEvents.head.name
    }

    interactionTransition.failureStrategy match {
      case FireEventAfterFailure(event) =>
        getOutputEventNameWithRetryStrategyFiltered(event, interactionTransition.eventsToFire)
      case FireFunctionalEventAfterFailure(event) =>
        getOutputEventNameWithRetryStrategyFiltered(event, interactionTransition.eventsToFire)
      case RetryWithIncrementalBackoff(_, _, _, _, Some(event), _) =>
        getOutputEventNameWithRetryStrategyFiltered(event, interactionTransition.eventsToFire)
      case RetryWithIncrementalBackoff(_, _, _, _, _, Some(event)) =>
        getOutputEventNameWithRetryStrategyFiltered(event, interactionTransition.eventsToFire)
      case RetryWithIncrementalBackoff(_, _, _, _, None, _) =>
        getFirstOutputEventName(interactionTransition.eventsToFire)
      case BlockInteraction =>
        getFirstOutputEventName(interactionTransition.eventsToFire)
      case _ =>
        log.error("Delayed transition firing with unrecognised Failure Strategy")
        getFirstOutputEventName(interactionTransition.eventsToFire)
    }
  }

  private val javaDuration = FromValue[java.time.Duration]()
  private val finiteDuration = FromValue[FiniteDuration]()

  def getWaitTimeInMillis(interactionTransition: InteractionTransition, state: RecipeInstanceState): Long = {
    val input: immutable.Seq[IngredientInstance] = RecipeRuntime.createInteractionInput(interactionTransition, state)
    if (input.size != 1) throw new FatalInteractionException(s"Delayed transitions can only have 1 input ingredient")
    input.head.value match {
      case javaDuration(d) => d.toMillis
      case finiteDuration(fd) => fd.toMillis
      case _ => throw new FatalInteractionException(s"Delayed transition ingredient not of type scala.concurrent.duration.FiniteDuration or java.time.Duration")
    }
  }
}

/**
 * This actor is responsible for maintaining the state of a single petri net instance.
 */
class ProcessInstance(
                       processType: String,
                       compiledRecipe: CompiledRecipe,
                       settings: Settings,
                       runtime: ProcessInstanceRuntime,
                       delayedTransitionActor: ActorRef)
  extends ProcessInstanceEventSourcing(compiledRecipe.petriNet, settings.encryption, runtime.eventSource) {

  import context.dispatcher

  // setting up receive timeout to stop actor, when it's not stopped by IdleStop message
  context.setReceiveTimeout(settings.idleTTL.getOrElse(15 minutes) * 2)

  override val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  override def preStart(): Unit = {
    log.info(s"ProcessInstance started: $recipeInstanceId")
  }

  override def postStop(): Unit = {
    log.info(s"ProcessInstance stopped: $recipeInstanceId")
  }

  val recipeInstanceId = context.self.path.name

  val executor = runtime.jobExecutor(petriNet)

  private val completionListeners: mutable.Set[ActorRef] = mutable.Set.empty

  private var eventListeners: mutable.Map[String, Set[ActorRef]] = mutable.Map.empty

  private def addEventListener(eventName: String, listener: ActorRef) = {
    val newSet = eventListeners.getOrElse(eventName, Set.empty) + listener
    eventListeners += (eventName -> newSet)
  }

  private def removeEventListener(eventName: String, listener: ActorRef) = {
    val newSet = eventListeners.getOrElse(eventName, Set.empty) - listener
    eventListeners += (eventName -> newSet)
  }

  override def persistenceId: String = recipeInstanceId2PersistenceId(processType, recipeInstanceId)

  override def receiveCommand: Receive = uninitialized

  private def marshallMarking(marking: Marking[Any]): Marking[Id] = marking.asInstanceOf[Marking[Place]].marshall

  private def mapStateToProtocol(instance: internal.Instance[RecipeInstanceState]): protocol.InstanceState = {
    protocol.InstanceState(
      instance.sequenceNr,
      instance.marking.marshall,
      instance.state match {
        case state: RecipeInstanceState =>
          filterIngredientValuesFromState(state)
        case _ => instance.state
      },
      instance.jobs.view.map { case (key, value) => (key, mapJobsToProtocol(value)) }.toMap
    )
  }

  private def mapJobsToProtocol(job: internal.Job[RecipeInstanceState]): protocol.JobState =
    protocol.JobState(job.id, job.transition.getId, job.consume.marshall, job.input, job.failure.map(mapExceptionTateToProtocol))

  private def mapExceptionTateToProtocol(exceptionState: internal.ExceptionState): protocol.ExceptionState =
    protocol.ExceptionState(exceptionState.failureCount, exceptionState.failureReason, mapExceptionStrategyToProtocol(exceptionState.failureStrategy))

  private def mapExceptionStrategyToProtocol(strategy: internal.ExceptionStrategy): protocol.ExceptionStrategy = strategy match {
    case internal.ExceptionStrategy.BlockTransition => protocol.ExceptionStrategy.BlockTransition
    case internal.ExceptionStrategy.RetryWithDelay(delay) => protocol.ExceptionStrategy.RetryWithDelay(delay)
    case internal.ExceptionStrategy.Continue(marking, output) => protocol.ExceptionStrategy.Continue(marking.asInstanceOf[Marking[Place]].marshall, output)
    case internal.ExceptionStrategy.ContinueAsFunctionalEvent(marking, output) => protocol.ExceptionStrategy.ContinueAsFunctional(marking.asInstanceOf[Marking[Place]].marshall, output)
  }

  private def stopMe(): Unit = {
    context.parent ! Passivate(ProcessInstanceProtocol.Stop)
  }

  def uninitialized: Receive = {
    case Initialize(initialMarking, state) =>

      val uninitialized = Instance.uninitialized[RecipeInstanceState](petriNet)
      val event = InitializedEvent(initialMarking, state)

      // persist the initialized event
      persistEvent(uninitialized, event) {
        eventSource.apply(uninitialized)
          .andThen(step)
          .andThen {
            case (updatedInstance, _) =>

              // notifies the sender that initialization was successful
              sender() ! Initialized(initialMarking, state)

              // update the state
              context become running(updatedInstance, Map.empty)
          }
      }

    case Stop(_) =>
      log.info("Stop called in uninitialized")
      context.stop(self)

    case c: Command =>
      log.warning(s"Received unexpected command in uninitialized state: ${c.getClass.getName}")
      sender() ! Uninitialized(recipeInstanceId)
      stopMe()

    case ReceiveTimeout =>
      log.warning(s"${persistenceId}: Receive timeout received in uninitialized state")
      stopMe()
  }

  def waitForDeleteConfirmation(instance: Instance[RecipeInstanceState]): Receive = {
    case DeleteMessagesSuccess(toSequenceNr) =>
      log.processHistoryDeletionSuccessful(recipeInstanceId, toSequenceNr)
      context.stop(self)

    case DeleteMessagesFailure(cause, toSequenceNr) =>
      log.processHistoryDeletionFailed(recipeInstanceId, toSequenceNr, cause)
      context become running(instance, Map.empty)

    case ReceiveTimeout =>
      log.warning(s"${persistenceId}: Receive timeout received in delete confirmation state")
      context.stop(context.self)
  }

  private def filterIngredientValuesFromState(state: RecipeInstanceState): RecipeInstanceState = {
    state.copy(ingredients = filterIngredients(state.ingredients, settings.getIngredientsFilter))
  }

  private def filterIngredientValuesFromEventInstance(eventInstance: Any): Any = {
    if (eventInstance == null) {
      eventInstance
    } else eventInstance match {
      case casted: EventInstance =>
        if (casted.providedIngredients != null && casted.providedIngredients.nonEmpty)
          casted.copy(providedIngredients = filterIngredients(casted.providedIngredients, settings.providedIngredientFilter))
        else
          casted
      case _ => eventInstance
    }
  }

  private def updateState(updatedInstance: Instance[RecipeInstanceState], scheduledRetries: Map[Long, Cancellable], firedEvent: Option[EventInstance] = None): Unit = {

    // Check for Event Occurrences
    firedEvent.foreach { event =>
      val eventName = event.name
      // Find listeners for this specific event
      eventListeners.get(eventName).foreach { listenersForThisEvent =>
        // Notify them
        listenersForThisEvent.foreach(listener => {
          listener ! EventOccurred
        })
        // Remove them from the map
        eventListeners.remove(eventName)
      }
    }

    // Check for Idle Condition
    if (updatedInstance.hasCompletedExecution) {
      // Notify all idle waiters
      completionListeners.foreach(listener => {
        listener ! Completed
      })
      // Clear the idle waiters list
      // Actors run in single thread so there is no race condition to be cautious of with this.
      completionListeners.clear()
    }

    context become running(updatedInstance, scheduledRetries)
  }

  def running(instance: Instance[RecipeInstanceState],
              scheduledRetries: Map[Long, Cancellable]): Receive = {
    case Stop(deleteHistory) =>
      scheduledRetries.values.foreach(_.cancel())
      if (deleteHistory) {
        log.debug("Deleting recipe instance history")
        deleteMessages(lastSequenceNr)
        context become waitForDeleteConfirmation(instance)
      } else
        context.stop(self)

    case IdleStop(n) =>
      if (n == instance.sequenceNr && instance.activeJobs.isEmpty) {
        log.idleStop(recipeInstanceId, settings.idleTTL.getOrElse(Duration.Zero))
        stopMe()
      }

    case ReceiveTimeout =>
      if (instance.activeJobs.isEmpty) {
        log.warning(s"Process $persistenceId has been stopped by idle timeout")
        stopMe()
      } else {
        log.debug("Receive timeout happened but jobs are still active: will wait for another receive timeout")
      }

    case ProcessInstanceProtocol.AwaitCompleted =>
      if (instance.hasCompletedExecution) {
        sender() ! ProcessInstanceProtocol.Completed
      }
      else {
        // Register listener
        completionListeners += sender()
        // Check to avoid race condition
        if (instance.hasCompletedExecution) {
          completionListeners -= sender()
          sender() ! ProcessInstanceProtocol.Completed
        }
    }

    case ProcessInstanceProtocol.AwaitEvent(eventName) =>
      println(s"Awaiting event $eventName")
      val state = instance.state

      if (state.eventNames.contains(eventName)) {
        println(s"Awaiting event $eventName 1")
        sender() ! ProcessInstanceProtocol.EventOccurred
      }
      else {
        println(s"Awaiting event $eventName 2")
        // Register listener
        addEventListener(eventName, sender())
        // Check to avoid race condition
        if (state.eventNames.contains(eventName)) {
          removeEventListener(eventName, sender())
          sender() ! ProcessInstanceProtocol.EventOccurred
        }
      }

    case GetState =>
      sender() ! mapStateToProtocol(instance)

    case GetIngredient(name) =>
      instance.state match {
        case state: RecipeInstanceState =>
          state.ingredients.get(name) match {
            case Some(value) => sender() ! IngredientFound(value)
            case None => sender() ! IngredientNotFound
          }
        case _ =>
          sender() ! IngredientNotFound
      }

    case AddMetaData(metaData: Map[String, String]) =>
      persistEvent(instance, ProcessInstanceEventSourcing.MetaDataAdded(metaData))(
        eventSource.apply(instance)
          .andThen {
            case (instance) =>
              sender() ! ProcessInstanceProtocol.MetaDataAdded
              updateState(instance, scheduledRetries)
          })

    case event@TransitionFiredEvent(jobId, transitionId, correlationId, timeStarted, timeCompleted, consumed, produced, output) =>
      val transition = instance.petriNet.transitions.getById(transitionId)
      log.transitionFired(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, transition, jobId, timeStarted, timeCompleted)
      // persist the success event
      persistEvent(instance, event)(
        eventSource.apply(instance)
          .andThen(step)
          .andThen {
            case (updatedInstance, newJobs) =>
              // the sender is notified of the transition having fired
              sender() ! TransitionFired(jobId, transitionId, correlationId, consumed, produced, newJobs.map(_.id), filterIngredientValuesFromEventInstance(output))

              // the job is removed from the state since it completed
              // Safely convert output to Option[EventInstance]
              val firedEventOpt = Option(output).map(_.asInstanceOf[EventInstance])
              updateState(updatedInstance, scheduledRetries - jobId, firedEventOpt)
          }
      )

    case event@TransitionFailedWithOutputEvent(jobId, transitionId, correlationId, timeStarted, timeCompleted, consumed, produced, output) =>
      val transition = instance.petriNet.transitions.getById(transitionId)
      log.transitionFired(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, transition, jobId, timeStarted, timeCompleted)
      // persist the success event
      persistEvent(instance, event)(
        eventSource.apply(instance)
          .andThen(step)
          .andThen {
            case (updatedInstance, newJobs) =>
              // the sender is notified of the transition having fired
              sender() ! TransitionFired(jobId, transitionId, correlationId, consumed, produced, newJobs.map(_.id), filterIngredientValuesFromEventInstance(output))

              // the job is removed from the state since it completed
              updateState(updatedInstance, scheduledRetries - jobId)
          }
      )

    //TODO modify this
    case event@TransitionFailedWithFunctionalOutputEvent(jobId, transitionId, correlationId, timeStarted, timeCompleted, consumed, produced, output) =>
      val transition = instance.petriNet.transitions.getById(transitionId)
      log.transitionFired(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, transition, jobId, timeStarted, timeCompleted)
      // persist the success event
      persistEvent(instance, event)(
        eventSource.apply(instance)
          .andThen(step)
          .andThen {
            case (updatedInstance, newJobs) =>
              // the sender is notified of the transition having fired
              sender() ! TransitionFired(jobId, transitionId, correlationId, consumed, produced, newJobs.map(_.id), filterIngredientValuesFromEventInstance(output))

              // the job is removed from the state since it completed
              updateState(updatedInstance, scheduledRetries - jobId)
          }
      )

    case ProcessInstanceProtocol.TransitionDelayed(jobId, transitionId, consumed) =>
      val internalEvent = ProcessInstanceEventSourcing.TransitionDelayed(jobId, transitionId, consumed)
      // persist the event
      persistEvent(instance, internalEvent)(
        eventSource.apply(instance)
          .andThen { case updatedInstance: Instance[RecipeInstanceState] =>
            if (updatedInstance.activeJobs.isEmpty) {
              startIdleStop(updatedInstance.sequenceNr)
            }
            updateState(updatedInstance, scheduledRetries - jobId)
          }
      )

    case ProcessInstanceProtocol.DelayedTransitionFired(jobId, transitionId, eventToFire) =>
      if (instance.delayedTransitionIds.contains(transitionId) && instance.delayedTransitionIds(transitionId) > 0) {
        val transition = petriNet.transitions.getById(transitionId, "transition in petrinet")
        val out: EventInstance = EventInstance.apply(eventToFire)

        //TODO create a better way to get the outgoing places (not by directly calling the RecipeRuntime)
        val produced = RecipeRuntime.createProducedMarking(
          petriNet.outMarking(transition),
          Some(out)
        ).marshall
        val internalEvent = ProcessInstanceEventSourcing.DelayedTransitionFired(jobId, transitionId, System.currentTimeMillis(), produced, out)

        val timestamp = System.currentTimeMillis()
        log.transitionFired(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, transition, jobId, timestamp, timestamp)

        LogAndSendEvent.eventFired(EventFired(timestamp, compiledRecipe.name, compiledRecipe.recipeId, recipeInstanceId, out.name), context.system.eventStream)

        persistEvent(instance, internalEvent)(
          eventSource.apply(instance)
            .andThen(step)
            .andThen {
              case (updatedInstance, newJobs) =>
                // the sender is notified of the transition having fired
                sender() ! TransitionFired(jobId, transitionId, None, null, produced, newJobs.map(_.id), filterIngredientValuesFromEventInstance(out))
                // The DelayedTransition is acknowledged so that it is removed
                delayedTransitionActor ! FireDelayedTransitionAck(recipeInstanceId, jobId)

                // Pass the fired event to updateState to notify listeners and remove the job
                updateState(updatedInstance, scheduledRetries - jobId, Some(out))
            }
        )
      } else {
        log.warning(s"Ignoring DelayedTransitionFired since there is no open asyncConsumedMarkings for transition: $transitionId with count: ${instance.delayedTransitionIds.get(transitionId)}")
        //The DelayedTransition is acknowledged so that it is removed from the DelayedTransitionManager.
        delayedTransitionActor ! FireDelayedTransitionAck(recipeInstanceId, jobId)
      }

    case event@TransitionFailedEvent(jobId, transitionId, correlationId, timeStarted, timeFailed, consume, input, reason, strategy) =>

      val transition = instance.petriNet.transitions.getById(transitionId)

      log.transitionFailed(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, transition, jobId, timeStarted, timeFailed, reason)

      strategy match {
        case RetryWithDelay(delay) =>

          log.scheduleRetry(recipeInstanceId, transition, delay)

          val originalSender = sender()

          // persist the failure event
          persistEvent(instance, event)(
            eventSource.apply(instance)
              .andThen { updatedInstance =>

                // a retry is scheduled on the scheduler of the actor system
                val retry = system.scheduler.scheduleOnce(delay milliseconds) {
                  executeJob(updatedInstance.jobs(jobId), originalSender)
                }

                // the sender is notified of the failed transition
                sender() ! TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, mapExceptionStrategyToProtocol(strategy))

                // the state is updated
                updateState(updatedInstance, scheduledRetries + (jobId -> retry))
              }
          )

        case Continue(produced, out) =>
          val transitionFailedWithOutput = TransitionFailedWithOutputEvent(
            jobId, transitionId, correlationId, timeStarted, timeFailed, consume, marshallMarking(produced), out)

          persistEvent(instance, transitionFailedWithOutput)(
            eventSource.apply(instance)
              .andThen(step)
              .andThen { case (updatedInstance, newJobs) =>
                sender() ! TransitionFired(jobId, transitionId, correlationId, consume, marshallMarking(produced), newJobs.map(_.id), filterIngredientValuesFromEventInstance(out))
                updateState(updatedInstance, scheduledRetries - jobId)
              })

        case ContinueAsFunctionalEvent(produced, out) =>
          val transitionFailedWithOutput = TransitionFailedWithFunctionalOutputEvent(
            jobId, transitionId, correlationId, timeStarted, timeFailed, consume, marshallMarking(produced), out)

          persistEvent(instance, transitionFailedWithOutput)(
            eventSource.apply(instance)
              .andThen(step)
              .andThen { case (updatedInstance, newJobs) =>
                sender() ! TransitionFired(jobId, transitionId, correlationId, consume, marshallMarking(produced), newJobs.map(_.id), filterIngredientValuesFromEventInstance(out))
                updateState(updatedInstance, scheduledRetries - jobId)
              })

        case _ =>
          persistEvent(instance, event)(
            eventSource.apply(instance)
              .andThen { updatedInstance =>
                sender() ! TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, mapExceptionStrategyToProtocol(strategy))
                updateState(updatedInstance, scheduledRetries - jobId)
              })
      }

    case FireTransition(transitionId, input, correlationIdOption) =>

      /**
       * TODO
       *
       * This should only return once the initial transition is completed & persisted
       * That way we are sure the correlation id is persisted.
       */
      val transition = petriNet.transitions.getById(transitionId, "transition in petrinet")

      correlationIdOption match {
        case Some(correlationId) if instance.hasReceivedCorrelationId(correlationId) =>
          sender() ! FireSensoryEventRejection.AlreadyReceived(recipeInstanceId, correlationId)
        case _ =>
          runtime.createJob(transition, input, correlationIdOption).run(instance).value match {
            case (updatedInstance, Right(job)) =>
              executeJob(job, sender())
              updateState(updatedInstance, scheduledRetries)
            case (_, Left(reason)) =>

              log.fireTransitionRejected(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, transition, reason)

              sender() ! FireSensoryEventRejection.FiringLimitMet(recipeInstanceId)
          }
      }

    case Initialize(_, _) =>
      sender() ! AlreadyInitialized(recipeInstanceId)

    case OverrideExceptionStrategy(jobId, protocol.ExceptionStrategy.RetryWithDelay(timeout)) =>

      instance.jobs.get(jobId) match {
        // retry is only allowed if the interaction is blocked by a failure
        case Some(job@internal.Job(_, _, _, _, _, _, Some(blocked@internal.ExceptionState(_, _, _, internal.ExceptionStrategy.BlockTransition)))) =>

          // the job is updated so it cannot be retried again
          val updatedJob: Job[RecipeInstanceState] = job.copy(failure = Some(blocked.copy(failureStrategy = internal.ExceptionStrategy.RetryWithDelay(timeout))))
          val updatedInstance: Instance[RecipeInstanceState] = instance.copy(jobs = instance.jobs + (jobId -> updatedJob))
          val originalSender = sender()

          // execute the job immediately if there is no timeout
          if (timeout == 0) {
            executeJob(job, originalSender)
          }
          else {
            // schedule the retry
            val scheduledRetry = system.scheduler.scheduleOnce(timeout millisecond)(executeJob(job, originalSender))

            // switch to the new state
            updateState(updatedInstance, scheduledRetries + (jobId -> scheduledRetry))
          }

        case Some(_) =>
          sender() ! InvalidCommand(s"Job with id '$jobId' is not blocked")

        case None =>
          sender() ! InvalidCommand(s"Job with id '$jobId' does not exist")
      }

    case OverrideExceptionStrategy(jobId, protocol.ExceptionStrategy.Continue(produce, output)) =>

      instance.jobs.get(jobId) match {
        // resolving is only allowed if the interaction is blocked by a failure
        case Some(internal.Job(_, correlationId, _, transition, consumed, _, Some(internal.ExceptionState(_, _, _, internal.ExceptionStrategy.BlockTransition)))) =>

          val producedMarking: Marking[Place] = produce.unmarshall(petriNet.places)

          // the provided marking must be valid according to the petri net
          if (petriNet.outMarking(transition) != producedMarking.multiplicities)
            sender() ! InvalidCommand(s"Invalid marking provided")
          else {

            // to resolve the failure a successful TransitionFiredEvent is created
            val event = TransitionFiredEvent(jobId, transition.getId, correlationId, System.currentTimeMillis(), System.currentTimeMillis(), consumed.marshall, produce, output)

            // and processed synchronously
            running(instance, scheduledRetries).apply(event)
          }

        case Some(_) =>
          sender() ! InvalidCommand(s"Job with id '$jobId' is not blocked")

        case None =>
          sender() ! InvalidCommand(s"Job with id '$jobId' does not exist")
      }

    case OverrideExceptionStrategy(jobId, protocol.ExceptionStrategy.BlockTransition) =>

      instance.jobs.get(jobId) match {
        // blocking is only allowed when the interaction is currently retrying
        case Some(job@internal.Job(_, correlationId, _, transition, consumed, _, Some(internal.ExceptionState(_, _, failureReason, internal.ExceptionStrategy.RetryWithDelay(_))))) =>

          if (scheduledRetries(jobId).cancel()) {

            val now = System.currentTimeMillis()

            // to block the interaction a failure event is created to prevent retry after reboot
            val event = TransitionFailedEvent(jobId, transition.getId, correlationId, now, now, consumed.marshall, job.input, failureReason, internal.ExceptionStrategy.BlockTransition)

            // and processed synchronously
            running(instance, scheduledRetries - jobId).apply(event)
          }

        case Some(_) =>
          sender() ! InvalidCommand(s"Job with id '$jobId' is not retrying")

        case None =>
          sender() ! InvalidCommand(s"Job with id '$jobId' does not exist")
      }
  }

  private def startIdleStop(sequenceNr: Long): Unit = {
    settings.idleTTL.foreach { ttl =>
      system.scheduler.scheduleOnce(ttl, context.self, IdleStop(sequenceNr))
    }
  }

  /**
   * This functions 'steps' the execution of the instance.
   *
   * It finds which transitions are enabled and executes those.
   */
  def step(instance: Instance[RecipeInstanceState]): (Instance[RecipeInstanceState], Set[Job[RecipeInstanceState]]) = {
    runtime.allEnabledJobs.run(instance).value match {
      case (updatedInstance, jobs) =>
        if (jobs.isEmpty && updatedInstance.activeJobs.isEmpty)
          startIdleStop(updatedInstance.sequenceNr)
        jobs.foreach(job => executeJob(job, sender()))
        (updatedInstance, jobs)
    }
  }

  def executeJob(job: Job[RecipeInstanceState], originalSender: ActorRef): Unit = {
    log.fireTransition(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, job.id, job.transition, System.currentTimeMillis())
    job.transition match {
      case _: EventTransition =>
        BakerLogging.default.firingEvent(recipeInstanceId, compiledRecipe.recipeId, compiledRecipe.name, job.id, job.transition, System.currentTimeMillis())
        executeJobViaExecutor(job, originalSender)
      case i: InteractionTransition if isDelayedInteraction(i) =>
        startDelayedTransition(i, job, originalSender)
      case i: InteractionTransition if isCheckpointEventInteraction(i) =>
        val event: TransitionFiredEvent = jobToFinishedInteraction(job, i.eventsToFire.head.name)

        val currentTime = System.currentTimeMillis()
        LogAndSendEvent.eventFired(EventFired(currentTime, compiledRecipe.name, compiledRecipe.recipeId, recipeInstanceId, i.eventsToFire.head.name), context.system.eventStream)

        self.tell(event, originalSender)
      case _ => executeJobViaExecutor(job, originalSender)
    }
  }

  def executeJobViaExecutor(job: Job[RecipeInstanceState], originalSender: ActorRef): Unit = {
    Try(context.self).foreach { self =>
      val io: IO[TransitionEvent] = executor(job).evalOn(settings.executionContext)
      io.unsafeRunAsync {
        case Right(event: TransitionEvent) => self.tell(event, originalSender)
        case Left(exception) => self.tell(Status.Failure(exception), originalSender)
      }(settings.ioRuntime)
    }
  }

  def jobToFinishedInteraction(job: Job[RecipeInstanceState], outputEventName: String): TransitionFiredEvent = {
    val startTime = System.currentTimeMillis()
    val outputEvent: EventInstance = EventInstance.apply(outputEventName)
    com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceEventSourcing.TransitionFiredEvent(
      job.id,
      job.transition.getId,
      job.correlationId,
      startTime,
      System.currentTimeMillis(),
      job.consume.marshall,

      RecipeRuntime.createProducedMarking(
        petriNet.outMarking(job.transition),
        Some(outputEvent)).marshall,
      outputEvent
    )
  }

  //TODO rewrite if statement,
  // This is a very naive implementation, the interface of the Interaction is not validated.
  // This only recognises the TimerInteractions as delayed interaction
  private def isDelayedInteraction(interactionTransition: InteractionTransition): Boolean = {
    interactionTransition.originalInteractionName == "TimerInteraction"
  }

  private def isCheckpointEventInteraction(interactionTransition: InteractionTransition): Boolean = {
    interactionTransition.interactionName.startsWith(checkpointEventInteractionPrefix)
  }

  def startDelayedTransition(interactionTransition: InteractionTransition, job: Job[RecipeInstanceState], originalSender: ActorRef): Unit = {
    delayedTransitionActor ! ScheduleDelayedTransition(
      recipeInstanceId,
      getWaitTimeInMillis(interactionTransition, job.processState),
      job.id,
      job.transition.getId,
      job.consume.marshall,
      getOutputEventName(interactionTransition, log),
      originalSender)
  }

  def scheduleFailedJobsForRetry(instance: Instance[RecipeInstanceState]): Map[Long, Cancellable] = {
    instance.jobs.values.foldLeft(Map.empty[Long, Cancellable]) {
      case (map, j@Job(_, _, _, _, _, _, Some(internal.ExceptionState(failureTime, _, _, RetryWithDelay(delay))))) =>
        val newDelay = failureTime + delay - System.currentTimeMillis()
        if (newDelay < 0) {
          executeJob(j, sender())
          map
        } else {
          log.scheduleRetry(recipeInstanceId, j.transition, newDelay)
          val cancellable = system.scheduler.scheduleOnce(newDelay milliseconds) {
            executeJob(j, sender())
          }
          map + (j.id -> cancellable)
        }
      case (acc, _) => acc
    }
  }

  override def onRecoveryCompleted(instance: Instance[RecipeInstanceState]) = {
    val scheduledRetries = scheduleFailedJobsForRetry(instance)
    val (updatedInstance, jobs) = step(instance)
    log.info(s"ProcessInstance: Finished receiveRecover " +
      s"for ${recipeInstanceId} " +
      s"with recipe: ${recipeInstanceId} with ${updatedInstance.state.events.size} events, " +
      s"${updatedInstance.state.ingredients.size} ingredients and " +
      s"${updatedInstance.activeJobs.size} active jobs")
    updateState(updatedInstance, scheduledRetries)
  }
}
