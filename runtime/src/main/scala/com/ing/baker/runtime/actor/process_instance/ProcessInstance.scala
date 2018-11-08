package com.ing.baker.runtime.actor.process_instance

import akka.actor._
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.pattern.pipe
import akka.persistence.{DeleteMessagesFailure, DeleteMessagesSuccess}
import cats.effect.IO
import cats.syntax.apply._
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.EventSourcing._
import com.ing.baker.petrinet.runtime.ExceptionStrategy.{Continue, RetryWithDelay}
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.actor.process_instance.ProcessInstance._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceLogger._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.{ExceptionState, ExceptionStrategy, _}
import com.ing.baker.runtime.actor.serialization.Encryption

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import scala.language.existentials
import scala.util.Try

object ProcessInstance {

  case class Settings(executionContext: ExecutionContext,
                      idleTTL: Option[FiniteDuration],
                      encryption: Encryption)

  private case class IdleStop(seq: Long) extends NoSerializationVerificationNeeded

  def persistenceIdPrefix(processType: String) = s"process-$processType-"

  def processId2PersistenceId(processType: String, processId: String): String = persistenceIdPrefix(processType) + processId

  def persistenceId2ProcessId(processType: String, persistenceId: String): Option[String] = {
    val parts = persistenceId.split(persistenceIdPrefix(processType))
    if (parts.length == 2)
      Some(parts(1))
    else
      None
  }
}

/**
  * This actor is responsible for maintaining the state of a single petri net instance.
  */
class ProcessInstance[P : Identifiable, T : Identifiable, S, E](
     processType: String,
     petriNet: PetriNet[P, T],
     settings: Settings,
     runtime: PetriNetRuntime[P, T, S, E]) extends ProcessInstanceRecovery[P, T, S, E](petriNet, settings.encryption, runtime.eventSource) {

  import context.dispatcher

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  val processId = context.self.path.name

  val executor = runtime.jobExecutor(petriNet)

  override def persistenceId: String = processId2PersistenceId(processType, processId)

  override def receiveCommand: Receive = uninitialized

  implicit def marshallMarking(marking: Marking[Any]): Marking[Id] = marking.asInstanceOf[Marking[P]].marshall

  implicit def fromExecutionInstance(instance: com.ing.baker.petrinet.runtime.Instance[P, T, S]): InstanceState =
    InstanceState(instance.sequenceNr, instance.marking.marshall, instance.state, instance.jobs.mapValues(fromExecutionJob(_)).map(identity))

  implicit def fromExecutionJob(job: com.ing.baker.petrinet.runtime.Job[P, T, S]): JobState =
    JobState(job.id, job.transition.getId, job.consume.marshall, job.input, job.failure.map(fromExecutionExceptionState))

  implicit def fromExecutionExceptionState(exceptionState: com.ing.baker.petrinet.runtime.ExceptionState): ExceptionState =
    ExceptionState(exceptionState.failureCount, exceptionState.failureReason, fromExecutionExceptionStrategy(exceptionState.failureStrategy))

  implicit def fromExecutionExceptionStrategy(strategy: com.ing.baker.petrinet.runtime.ExceptionStrategy): ExceptionStrategy = strategy match {
    case com.ing.baker.petrinet.runtime.ExceptionStrategy.Fatal => ExceptionStrategy.Fatal
    case com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition => ExceptionStrategy.BlockTransition
    case com.ing.baker.petrinet.runtime.ExceptionStrategy.RetryWithDelay(delay) => ExceptionStrategy.RetryWithDelay(delay)
    case com.ing.baker.petrinet.runtime.ExceptionStrategy.Continue(marking, output) => ExceptionStrategy.Continue(marking.asInstanceOf[Marking[P]].marshall, output)
  }

  def uninitialized: Receive = {
    case Initialize(initialMarking, state) ⇒

      val uninitialized = Instance.uninitialized[P, T, S](petriNet)
      val event = InitializedEvent(initialMarking, state)

      persistEvent(uninitialized, event) {
        eventSource.apply(uninitialized)
          .andThen(step)
          .andThen {
            case (updatedInstance, _) ⇒
              context become running(updatedInstance, Map.empty)
              sender() ! Initialized(initialMarking, state)
          }
      }

    case Stop(_) ⇒
      context.stop(context.self)

    case _: Command ⇒
      sender() ! Uninitialized(processId)
      context.stop(context.self)

  }

  def waitForDeleteConfirmation(instance: Instance[P, T, S]): Receive = {
    case DeleteMessagesSuccess(toSequenceNr) =>

      log.processHistoryDeletionSuccessful(processId, toSequenceNr)

      context.stop(context.self)
    case DeleteMessagesFailure(cause, toSequenceNr) =>
      log.processHistoryDeletionFailed(processId, toSequenceNr, cause)
      context become running(instance, Map.empty)
  }

  def running(instance: Instance[P, T, S],
              scheduledRetries: Map[Long, Cancellable]): Receive = {

    case Stop(deleteHistory) ⇒
      scheduledRetries.values.foreach(_.cancel())
      if(deleteHistory) {
        log.debug("Deleting process history")
        deleteMessages(lastSequenceNr)
        context become waitForDeleteConfirmation(instance)
      } else
        context.stop(context.self)

    case IdleStop(n) if n == instance.sequenceNr && instance.activeJobs.isEmpty ⇒
      log.idleStop(processId, settings.idleTTL.getOrElse(Duration.Zero))
      context.stop(context.self)

    case GetState ⇒
      sender() ! fromExecutionInstance(instance)

    case event @ TransitionFiredEvent(jobId, transitionId, correlationId, timeStarted, timeCompleted, consumed, produced, output) ⇒

      val transition = instance.process.transitions.getById(transitionId)

      log.transitionFired(processId, transition.toString, jobId, timeStarted, timeCompleted)

      persistEvent(instance, event)(
        eventSource.apply(instance)
          .andThen(step)
          .andThen {
            case (updatedInstance, newJobs) ⇒
              sender() ! TransitionFired(jobId, transitionId, correlationId, consumed, produced, updatedInstance, newJobs.map(_.id), output)
              context become running(updatedInstance, scheduledRetries - jobId)
              updatedInstance
          }
      )

    case event @ TransitionFailedEvent(jobId, transitionId, correlationId, timeStarted, timeFailed, consume, input, reason, strategy) ⇒

      val transition = instance.process.transitions.getById(transitionId)

      log.transitionFailed(processId, transition.toString, jobId, timeStarted, timeFailed, reason)

      strategy match {
        case RetryWithDelay(delay) ⇒

          log.scheduleRetry(processId, transition.toString, delay)

          val originalSender = sender()

          persistEvent(instance, event)(
            eventSource.apply(instance)
              .andThen { updatedInstance ⇒
                val retry = system.scheduler.scheduleOnce(delay milliseconds) {
                  executeJob(updatedInstance.jobs(jobId), originalSender)
                }
                sender() ! TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, strategy)
                context become running(updatedInstance, scheduledRetries + (jobId -> retry))
              }
          )

        case Continue(produced, out) =>
          val transitionFiredEvent = TransitionFiredEvent(
            jobId, transitionId, correlationId, timeStarted, timeFailed, consume, produced, out)

          persistEvent(instance, transitionFiredEvent)(
            eventSource.apply(instance)
              .andThen(step)
              .andThen { case (updatedInstance, newJobs) ⇒
                sender() ! TransitionFired(jobId, transitionId, correlationId, consume, produced, updatedInstance, newJobs.map(_.id), out)
                context become running(updatedInstance, scheduledRetries - jobId)
              })

        case _ ⇒
          persistEvent(instance, event)(
            eventSource.apply(instance)
              .andThen { updatedInstance ⇒
                sender() ! TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, strategy)
                context become running(updatedInstance, scheduledRetries - jobId)
              })
      }

    case FireTransition(transitionId, input, correlationIdOption) ⇒

      /**
        * TODO
        *
        * This should only return once the initial transition is completed & persisted
        * That way we are sure the correlation id is persisted.
        */
      val transition = petriNet.transitions.getById(transitionId, "transition in petrinet")

      correlationIdOption match {
        case Some(correlationId) if instance.hasReceivedCorrelationId(correlationId) =>
            sender() ! AlreadyReceived(correlationId)
        case _ =>
          runtime.createJob(transition, input, correlationIdOption).run(instance).value match {
            case (updatedInstance, Right(job)) ⇒
              executeJob(job, sender())
              context become running(updatedInstance, scheduledRetries)
            case (_, Left(reason)) ⇒

              log.fireTransitionRejected(processId, transition.toString, reason)

              sender() ! TransitionNotEnabled(transitionId, reason)
          }
      }

    case Initialize(_, _) ⇒
      sender() ! AlreadyInitialized(processId)
  }

  def step(instance: Instance[P, T, S]): (Instance[P, T, S], Set[Job[P, T, S]]) = {

    runtime.allEnabledJobs.run(instance).value match {
      case (updatedInstance, jobs) ⇒

        if (jobs.isEmpty && updatedInstance.activeJobs.isEmpty)
          settings.idleTTL.foreach { ttl ⇒
            system.scheduler.scheduleOnce(ttl, context.self, IdleStop(updatedInstance.sequenceNr))
          }

        jobs.foreach(job ⇒ executeJob(job, sender()))
        (updatedInstance, jobs)
    }
  }

  def executeJob(job: Job[P, T, S], originalSender: ActorRef): Unit = {

    log.firingTransition(processId, job.id, job.transition.toString, System.currentTimeMillis())

    // context.self can be potentially throw NullPointerException in non graceful shutdown situations
    Try(context.self).foreach { self =>

      // executes the IO task on the ExecutionContext
      val future = IO.shift(settings.executionContext) *> executor(job)

      // translate to future and pipes the result of the future back to the actor
      future.unsafeToFuture().pipeTo(self)(originalSender)
    }
  }

  def scheduleFailedJobsForRetry(instance: Instance[P, T, S]): Map[Long, Cancellable] = {
    instance.jobs.values.foldLeft(Map.empty[Long, Cancellable]) {
      case (map, j @ Job(_, _, _, _, _, _, Some(com.ing.baker.petrinet.runtime.ExceptionState(failureTime, _, _, RetryWithDelay(delay))))) ⇒
        val newDelay = failureTime + delay - System.currentTimeMillis()
        if (newDelay < 0) {
          executeJob(j, sender())
          map
        } else {
          log.scheduleRetry(processId, j.transition.toString, newDelay)
          val cancellable = system.scheduler.scheduleOnce(newDelay milliseconds) { executeJob(j, sender()) }
          map + (j.id -> cancellable)
        }
      case (acc, _) ⇒ acc
    }
  }

  override def onRecoveryCompleted(instance: Instance[P, T, S]) = {
    val scheduledRetries = scheduleFailedJobsForRetry(instance)
    val (updatedInstance, jobs) = step(instance)
    context become running(updatedInstance, scheduledRetries)
  }
}
