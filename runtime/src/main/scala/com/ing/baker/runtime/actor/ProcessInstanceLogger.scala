package com.ing.baker.runtime.actor

import akka.event.Logging
import akka.event.Logging.LogLevel
import akka.persistence.PersistentActor
import com.ing.baker.runtime.actor.ProcessInstanceLogger.LogEvent

import scala.collection.JavaConverters._
import scala.concurrent.duration._

object ProcessInstanceLogger {

  sealed trait LogEvent {
    def mdc: Map[String, Any]
    def msg: String
  }

  case class LogIdleStop(processId: String, idleTTL: FiniteDuration) extends LogEvent {
    val mdc = Map("processId" -> processId)
    val msg = s"Instance was idle for $idleTTL, stopping the actor"
  }

  case class LogFireTransitionRejected(processId: String, transitionId: String, rejectReason: String) extends LogEvent {
    def mdc = Map(
      "processEvent" -> "FireTransitionRejected",
      "processId" -> processId,
      "transitionId" -> transitionId,
      "rejectReason" -> rejectReason)

    def msg = s"Not Firing Transition '$transitionId' because: $rejectReason"
  }

  case class LogTransitionFired(processId: String, transitionId: String, jobId: Long, timeStarted: Long, timeCompleted: Long) extends LogEvent {
    def mdc = Map(
      "processEvent" -> "TransitionFired",
      "processId" -> processId,
      "jobId" -> jobId,
      "transitionId" -> transitionId,
      "timeStarted" -> timeStarted,
      "timeCompleted" -> timeCompleted,
      "duration" -> (timeCompleted - timeStarted)
    )

    val msg = s"Transition '$transitionId' successfully fired"
  }
  case class LogTransitionFailed(processId: String, transitionId: String, jobId: Long, timeStarted: Long, timeFailed: Long, failureReason: String) extends LogEvent {
    def mdc = Map(
      "processEvent" -> "TransitionFailed",
      "processId" -> processId,
      "timeStarted" -> timeStarted,
      "timeFailed" -> timeFailed,
      "duration" -> (timeFailed - timeStarted),
      "transitionId" -> transitionId,
      "failureReason" -> failureReason
    )

    val msg = s"Transition '$transitionId' failed with: $failureReason"
  }

  import org.joda.time.format.PeriodFormatterBuilder
  val duration = new org.joda.time.Duration(123456)
  // in milliseconds

  val durationFormatter = new PeriodFormatterBuilder()
    .appendDays.appendSuffix("d")
    .appendSeparator(" ")
    .appendHours.appendSuffix("h")
    .appendSeparator(" ")
    .appendMinutes.appendSuffix("m")
    .appendSeparator(" ")
    .appendSeconds.appendSuffix("s")
    .appendSeparator(" ")
    .appendMillis.appendSuffix("ms")
    .appendSeparator(" ")
    .toFormatter

  case class LogScheduleRetry(processId: String, transitionId: String, delay: Long) extends LogEvent {
    def mdc = Map(
      "processEvent" -> "TransitionRetry",
      "processId" -> processId,
      "transitionId" -> transitionId)

    def msg = s"Scheduling a retry of transition '$transitionId' in ${durationFormatter.print(new org.joda.time.Duration(delay).toPeriod)}"
  }

  case class LogFiringTransition(processId: String, jobId: Long, transitionId: String, timeStarted: Long) extends LogEvent {
    def mdc = Map(
      "processEvent" -> "FiringTransition",
      "processId" -> processId,
      "jobId" -> jobId,
      "transitionId" -> transitionId,
      "timeStarted" -> timeStarted
    )
    def msg = s"Firing transition $transitionId"
  }
}

trait ProcessInstanceLogger {

  this: PersistentActor ⇒

  val log = Logging.getLogger(this)

  def logEvent(level: Logging.LogLevel, event: ⇒ LogEvent) = logWithMDC(level, event.msg, event.mdc)

  def logWithMDC(level: LogLevel, msg: String, mdc: Map[String, Any]) = {
    try {
      log.setMDC(mdc.asJava)
      log.log(level, msg)
    } finally {
      log.clearMDC()
    }
  }
}
