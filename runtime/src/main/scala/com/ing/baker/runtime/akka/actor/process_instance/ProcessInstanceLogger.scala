package com.ing.baker.runtime.akka.actor.process_instance

import akka.event.{DiagnosticLoggingAdapter, Logging}

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
        "RecipeInstanceId" -> recipeInstanceId
      )

      log.logWithMDC(Logging.DebugLevel, msg, mdc)
    }


    def processHistoryDeletionFailed(recipeInstanceId: String, toSequenceNr: Long, cause: Throwable) = {
      val msg = s"Process events are requested to be deleted up to $toSequenceNr sequence number, but delete operation failed."

      val mdc = Map(
        "RecipeInstanceId" -> recipeInstanceId
      )

      log.errorWithMDC(msg, mdc, cause)
    }

    def transitionFired(recipeInstanceId: String, transitionId: String, jobId: Long, timeStarted: Long, timeCompleted: Long) = {

      val mdc = Map(
        "processEvent" -> "TransitionFired",
        "RecipeInstanceId" -> recipeInstanceId,
        "jobId" -> jobId,
        "transitionId" -> transitionId,
        "timeStarted" -> timeStarted,
        "timeCompleted" -> timeCompleted,
        "duration" -> (timeCompleted - timeStarted)
      )

      val msg = s"Transition '$transitionId' successfully fired"

      log.logWithMDC(Logging.DebugLevel, msg, mdc)
    }

    def transitionFailed(recipeInstanceId: String, transitionId: String, jobId: Long, timeStarted: Long, timeFailed: Long, failureReason: String) {
      val mdc = Map(
        "processEvent" -> "TransitionFailed",
        "RecipeInstanceId" -> recipeInstanceId,
        "timeStarted" -> timeStarted,
        "timeFailed" -> timeFailed,
        "duration" -> (timeFailed - timeStarted),
        "transitionId" -> transitionId,
        "failureReason" -> failureReason
      )

      val msg = s"Transition '$transitionId' failed with: $failureReason"

      log.logWithMDC(Logging.ErrorLevel, msg, mdc)
    }

    def firingTransition(recipeInstanceId: String, jobId: Long, transitionId: String, timeStarted: Long): Unit = {
      val mdc = Map(
        "processEvent" -> "FiringTransition",
        "RecipeInstanceId" -> recipeInstanceId,
        "jobId" -> jobId,
        "transitionId" -> transitionId,
        "timeStarted" -> timeStarted
      )
      val msg = s"Firing transition $transitionId"

      log.logWithMDC(Logging.DebugLevel, msg, mdc)
    }

    def idleStop(recipeInstanceId: String, idleTTL: FiniteDuration)  {
      val mdc = Map("RecipeInstanceId" -> recipeInstanceId)
      val msg = s"Instance was idle for $idleTTL, stopping the actor"

      log.logWithMDC(Logging.DebugLevel, msg, mdc)
    }

    def fireTransitionRejected(recipeInstanceId: String, transitionId: String, rejectReason: String) {
      val mdc = Map(
        "processEvent" -> "FireTransitionRejected",
        "RecipeInstanceId" -> recipeInstanceId,
        "transitionId" -> transitionId,
        "rejectReason" -> rejectReason)

      val msg = s"Not Firing Transition '$transitionId' because: $rejectReason"

      log.logWithMDC(Logging.WarningLevel, msg, mdc)
    }

    def scheduleRetry(recipeInstanceId: String, transitionId: String, delay: Long) {
      val mdc = Map(
        "processEvent" -> "TransitionRetry",
        "RecipeInstanceId" -> recipeInstanceId,
        "transitionId" -> transitionId)

      val msg = s"Scheduling a retry of transition '$transitionId' in ${durationFormatter.print(new org.joda.time.Period(delay))}"

      log.logWithMDC(Logging.InfoLevel, msg, mdc)
    }
  }
}
