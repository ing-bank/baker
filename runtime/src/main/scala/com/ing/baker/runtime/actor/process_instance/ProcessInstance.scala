package com.ing.baker.runtime.actor.process_instance

import akka.actor._
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.pattern.pipe
import akka.persistence.{DeleteMessagesFailure, DeleteMessagesSuccess}
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.EventSourcing._
import com.ing.baker.petrinet.runtime.ExceptionStrategy.{Continue, RetryWithDelay}
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.actor.InternalBakerMessage
import com.ing.baker.runtime.actor.process_instance.ProcessInstance._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceLogger._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.serialization.Encryption
import fs2.Strategy

import scala.concurrent.duration._
import scala.language.existentials
import scala.util.Try

object ProcessInstance {

  case class Settings(
                       evaluationStrategy: Strategy,
                       idleTTL: Option[FiniteDuration],
                       encryption: Encryption)

  private case class IdleStop(seq: Long) extends InternalBakerMessage

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
class ProcessInstance[P[_], T[_, _], S, E](processType: String,
                                            processTopology: PetriNet[P[_], T[_, _]],
                                            settings: Settings,
                                            runtime: PetriNetRuntime[P, T, S, E],
                                            override implicit val placeIdentifier: Identifiable[P[_]],
                                            override implicit val transitionIdentifier: Identifiable[T[_, _]]) extends ProcessInstanceRecovery[P, T, S, E](processTopology, settings.encryption, runtime.eventSourceFn) {


  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  val processId = context.self.path.name

  override def persistenceId: String = processId2PersistenceId(processType, processId)

  import context.dispatcher

  val executor = runtime.jobExecutor.apply(topology)(settings.evaluationStrategy)

  override def receiveCommand = uninitialized

  def uninitialized: Receive = {
    case Initialize(markingData, state) ⇒

      val initialMarking = unmarshal[P](markingData, id => topology.places.getById(id, "place in petrinet"))
      val uninitialized = Instance.uninitialized[P, T, S](topology)
      val event = InitializedEvent(initialMarking, state)

      system.eventStream.publish(ProcessInstanceEvent(processType, processId, event))

      persistEvent(uninitialized, event) {
        eventSource.apply(uninitialized)
          .andThen(step)
          .andThen {
            case (updatedInstance, _) ⇒
              context become running(updatedInstance, Map.empty)
              sender() ! Initialized(marshal(initialMarking), state)
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
      log.debug(s"Process history successfully deleted (up to event sequence $toSequenceNr), stopping the actor")
      context.stop(context.self)
    case DeleteMessagesFailure(cause, toSequenceNr) =>
      log.error(cause, s"Process events are requested to be deleted up to $toSequenceNr sequence number, but delete operation failed.")
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

    case event@TransitionFiredEvent(jobId, t, correlationId, timeStarted, timeCompleted, consumed, produced, output) ⇒

      val transition = t.asInstanceOf[T[_, _]]
      val transitionId = transitionIdentifier(transition).value

      system.eventStream.publish(ProcessInstanceEvent(processType, processId, event))
      log.transitionFired(processId, transition.toString, jobId, timeStarted, timeCompleted)

      persistEvent(instance, event)(
        eventSource.apply(instance)
          .andThen(step)
          .andThen {
            case (updatedInstance, newJobs) ⇒
              sender() ! TransitionFired(jobId, transitionId, correlationId, marshal[P](consumed.asInstanceOf[Marking[P]]), marshal[P](produced.asInstanceOf[Marking[P]]), fromExecutionInstance(updatedInstance), newJobs.map(_.id))
              context become running(updatedInstance, scheduledRetries - jobId)
              updatedInstance
          }
      )

    case event@TransitionFailedEvent(jobId, t, correlationId, timeStarted, timeFailed, consume, input, reason, strategy) ⇒

      val transition = t.asInstanceOf[T[_, _]]
      val transitionId = transitionIdentifier(transition).value

      system.eventStream.publish(ProcessInstanceEvent(processType, processId, event))
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
                sender() ! TransitionFailed(jobId, transitionId, correlationId, marshal[P](consume.asInstanceOf[Marking[P]]), input, reason, strategy)
                context become running(updatedInstance, scheduledRetries + (jobId -> retry))
              }
          )

        case Continue(produced, out) =>
          val consumedMarking = consume.asInstanceOf[Marking[P]]
          val producedMarking = produced.asInstanceOf[Marking[P]]
          val transitionFiredEvent = TransitionFiredEvent[P, T, E](
            jobId, transition, correlationId, timeStarted, timeFailed, consumedMarking, producedMarking, out.asInstanceOf[E])

          persistEvent(instance, transitionFiredEvent)(
            eventSource.apply(instance)
              .andThen(step)
              .andThen { case (updatedInstance, newJobs) ⇒
                sender() ! TransitionFired(jobId, transitionId, correlationId, marshal[P](consumedMarking), marshal[P](producedMarking), fromExecutionInstance(updatedInstance), newJobs.map(_.id))
                context become running(updatedInstance, scheduledRetries - jobId)
              })

        case _ ⇒
          persistEvent(instance, event)(
            eventSource.apply(instance)
              .andThen { updatedInstance ⇒
                sender() ! TransitionFailed(jobId, transitionId, correlationId, marshal[P](consume.asInstanceOf[Marking[P]]), input, reason, strategy)
                context become running(updatedInstance, scheduledRetries - jobId)
              })
      }

    case FireTransition(transitionId, input, correlationIdOption) ⇒

      val transition = topology.transitions.getById(transitionId, "transition in petrinet").asInstanceOf[T[Any, Any]]

      def alreadyReceived(id: String) = instance.receivedCorrelationIds.contains(id) || instance.jobs.values.exists(_.correlationId == Some(id))

      correlationIdOption match {
        case Some(correlationId) if alreadyReceived(correlationId) =>
            sender() ! AlreadyReceived(correlationId)
        case _ =>
          runtime.jobPicker.createJob[S, Any, Any](transition, input, correlationIdOption).run(instance).value match {
            case (updatedInstance, Right(job)) ⇒
              executeJob(job, sender())
              context become running(updatedInstance, scheduledRetries)
            case (_, Left(reason)) ⇒

              log.fireTransitionRejected(processId, transition.toString, reason)

              sender() ! TransitionNotEnabled(transitionId, reason)
          }
      }

    case Initialize(_, _) ⇒
      sender() ! AlreadyInitialized
  }

  def step(instance: Instance[P, T, S]): (Instance[P, T, S], Set[Job[P, T, S, _]]) = {

    runtime.jobPicker.allEnabledJobs.run(instance).value match {
      case (updatedInstance, jobs) ⇒

        if (jobs.isEmpty && updatedInstance.activeJobs.isEmpty)
          settings.idleTTL.foreach { ttl ⇒
            system.scheduler.scheduleOnce(ttl, context.self, IdleStop(updatedInstance.sequenceNr))
          }

        jobs.foreach(job ⇒ executeJob(job, sender()))
        (updatedInstance, jobs)
    }
  }

  def executeJob[E](job: Job[P, T, S, E], originalSender: ActorRef) = {

    log.firingTransition(processId, job.id, job.transition.toString, System.currentTimeMillis())

    // context.self can be potentially throw NullPointerException in non graceful shutdown situations
    Try(context.self).foreach(executor(job).unsafeRunAsyncFuture().pipeTo(_)(originalSender))
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
