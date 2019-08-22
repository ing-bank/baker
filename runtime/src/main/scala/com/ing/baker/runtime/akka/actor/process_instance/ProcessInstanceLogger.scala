package com.ing.baker.runtime.akka.actor.process_instance

import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.il.petrinet.Transition

import scala.concurrent.duration._
import com.ing.baker.runtime.akka.actor.Util.logging._

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

    def processHistoryDeletionSuccessful(recipeInstanceId: String, toSequenceNr: Long) = {
      val msg = s"Process history successfully deleted (up to event sequence $toSequenceNr), stopping the actor"

      val mdc = Map(
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId
      )

      log.logWithMDC(Logging.InfoLevel, msg, mdc)
    }


    def processHistoryDeletionFailed(recipeInstanceId: String, toSequenceNr: Long, cause: Throwable) = {
      val msg = s"Process events are requested to be deleted up to $toSequenceNr sequence number, but delete operation failed."

      val mdc = Map(
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId
      )

      log.errorWithMDC(msg, mdc, cause)
    }

    def transitionFired(recipeInstanceId: String, transition: Transition, jobId: Long, timeStarted: Long, timeCompleted: Long) = {

      val mdc = Map(
        "processEvent" -> "TransitionFired",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "jobId" -> jobId,
        "transitionId" -> transition.label,
        "timeStarted" -> timeStarted,
        "timeCompleted" -> timeCompleted,
        "duration" -> (timeCompleted - timeStarted)
      )

      val msg = s"Transition '${transition.label}' successfully fired"

      log.logWithMDC(Logging.InfoLevel, msg, mdc)

      if(log.isDebugEnabled) {
        val debugMSG = s"Transition '${transition.toString}' successfully fired"
        log.logWithMDC(Logging.DebugLevel, debugMSG, mdc)
      }
    }

    def transitionFailed(recipeInstanceId: String, transition: Transition, jobId: Long, timeStarted: Long, timeFailed: Long, failureReason: String) {
      val mdc = Map(
        "processEvent" -> "TransitionFailed",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "timeStarted" -> timeStarted,
        "timeFailed" -> timeFailed,
        "duration" -> (timeFailed - timeStarted),
        "transitionId" -> transition.label,
        "failureReason" -> failureReason
      )

      val msg = s"Transition '${transition.label}' failed with: $failureReason"

      log.logWithMDC(Logging.ErrorLevel, msg, mdc)

      if(log.isDebugEnabled) {
        val debugMSG = s"Transition '${transition.toString}' failed with: $failureReason"
        log.logWithMDC(Logging.DebugLevel, debugMSG, mdc)
      }
    }

    def firingTransition(recipeInstanceId: String, jobId: Long, transition: Transition, timeStarted: Long): Unit = {
      val mdc = Map(
        "processEvent" -> "FiringTransition",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "jobId" -> jobId,
        "transitionId" -> transition.label,
        "timeStarted" -> timeStarted
      )
      val msg = s"Firing transition ${transition.label}"

      log.logWithMDC(Logging.InfoLevel, msg, mdc)

      if(log.isDebugEnabled) {
        val debugMSG = s"Firing transition ${transition.toString}"
        log.logWithMDC(Logging.DebugLevel, debugMSG, mdc)
      }
    }

    def idleStop(recipeInstanceId: String, idleTTL: FiniteDuration)  {
      val mdc = Map(
        "recipeInstanceId" -> recipeInstanceId,
        "processId" -> recipeInstanceId,
      )
      val msg = s"Instance was idle for $idleTTL, stopping the actor"

      log.logWithMDC(Logging.InfoLevel, msg, mdc)
    }

    def fireTransitionRejected(recipeInstanceId: String, transition: Transition, rejectReason: String) {
      val mdc = Map(
        "processEvent" -> "FireTransitionRejected",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "transitionId" -> transition.label,
        "rejectReason" -> rejectReason)

      val msg = s"Not Firing Transition '${transition.label}' because: $rejectReason"

      log.logWithMDC(Logging.WarningLevel, msg, mdc)
    }

    def scheduleRetry(recipeInstanceId: String, transition: Transition, delay: Long) {
      val mdc = Map(
        "processEvent" -> "TransitionRetry",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "transitionId" -> transition.label)

      val msg = s"Scheduling a retry of transition '${transition.label}' in ${durationFormatter.print(new org.joda.time.Period(delay))}"

      log.logWithMDC(Logging.InfoLevel, msg, mdc)
    }
  }
}
