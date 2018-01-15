package com.ing.baker.runtime.actor

import akka.event.Logging.LogLevel
import akka.event.{DiagnosticLoggingAdapter, Logging}

import scala.collection.JavaConverters._
import scala.concurrent.duration._

object ProcessInstanceLogger {

  import org.joda.time.format.PeriodFormatterBuilder

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

  implicit class LoggingAdapterFns(log: DiagnosticLoggingAdapter) {

    def transitionFired(processId: String, transitionId: String, jobId: Long, timeStarted: Long, timeCompleted: Long) = {

      val mdc = Map(
        "processEvent" -> "TransitionFired",
        "processId" -> processId,
        "jobId" -> jobId,
        "transitionId" -> transitionId,
        "timeStarted" -> timeStarted,
        "timeCompleted" -> timeCompleted,
        "duration" -> (timeCompleted - timeStarted)
      )

      val msg = s"Transition '$transitionId' successfully fired"

      logWithMDC(Logging.DebugLevel, msg, mdc)
    }

    def transitionFailed(processId: String, transitionId: String, jobId: Long, timeStarted: Long, timeFailed: Long, failureReason: String) {
      val mdc = Map(
        "processEvent" -> "TransitionFailed",
        "processId" -> processId,
        "timeStarted" -> timeStarted,
        "timeFailed" -> timeFailed,
        "duration" -> (timeFailed - timeStarted),
        "transitionId" -> transitionId,
        "failureReason" -> failureReason
      )

      val msg = s"Transition '$transitionId' failed with: $failureReason"

      logWithMDC(Logging.ErrorLevel, msg, mdc)
    }

    def firingTransition(processId: String, jobId: Long, transitionId: String, timeStarted: Long): Unit = {
      val mdc = Map(
        "processEvent" -> "FiringTransition",
        "processId" -> processId,
        "jobId" -> jobId,
        "transitionId" -> transitionId,
        "timeStarted" -> timeStarted
      )
      val msg = s"Firing transition $transitionId"

      logWithMDC(Logging.DebugLevel, msg, mdc)
    }

    def idleStop(processId: String, idleTTL: FiniteDuration)  {
      val mdc = Map("processId" -> processId)
      val msg = s"Instance was idle for $idleTTL, stopping the actor"

      logWithMDC(Logging.DebugLevel, msg, mdc)
    }

    def fireTransitionRejected(processId: String, transitionId: String, rejectReason: String) {
      val mdc = Map(
        "processEvent" -> "FireTransitionRejected",
        "processId" -> processId,
        "transitionId" -> transitionId,
        "rejectReason" -> rejectReason)

      val msg = s"Not Firing Transition '$transitionId' because: $rejectReason"

      logWithMDC(Logging.WarningLevel, msg, mdc)
    }


    def scheduleRetry(processId: String, transitionId: String, delay: Long) {
      val mdc = Map(
        "processEvent" -> "TransitionRetry",
        "processId" -> processId,
        "transitionId" -> transitionId)

      val msg = s"Scheduling a retry of transition '$transitionId' in ${durationFormatter.print(new org.joda.time.Period(delay))}"

      logWithMDC(Logging.InfoLevel, msg, mdc)
    }

    def logWithMDC(level: LogLevel, msg: String, mdc: Map[String, Any]) = {
      try {
        log.setMDC(mdc.asJava)
        log.log(level, msg)
      } finally {
        log.clearMDC()
      }
    }
  }
}
