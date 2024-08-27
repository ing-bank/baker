package com.ing.baker.runtime.akka.actor.process_instance

import akka.event.{DiagnosticLoggingAdapter, Logging}
import com.ing.baker.il.petrinet.Transition
import com.ing.baker.runtime.akka.actor.Util.logging._
import com.ing.baker.runtime.model.BakerLogging

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

    val bakerLogging: BakerLogging = BakerLogging.default

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

    def fireTransition(recipeInstanceId: String,
                       recipeId: String,
                       recipeName: String,
                       jobId: Long,
                       transition: Transition,
                       timeStarted: Long): Unit = {
      val mdc = Map(
        "processEvent" -> "FiringTransition",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "recipeName" -> recipeName,
        "recipeId" -> recipeId,
        "jobId" -> jobId,
        "transitionId" -> transition.label,
        "timeStarted" -> timeStarted
      )
      val msg = s"Firing transition ${transition.label}"
      log.logWithMDC(Logging.InfoLevel, msg, mdc)
    }

    def transitionFired(recipeInstanceId: String,
                        recipeId: String,
                        recipeName: String,
                        transition: Transition,
                        jobId: Long,
                        timeStarted: Long,
                        timeCompleted: Long) = {

      val mdc = Map(
        "processEvent" -> "TransitionFired",
        "processId" -> recipeInstanceId,
        "recipeName" -> recipeName,
        "recipeId" -> recipeId,
        "recipeInstanceId" -> recipeInstanceId,
        "jobId" -> jobId,
        "transitionId" -> transition.label,
        "timeStarted" -> timeStarted,
        "timeCompleted" -> timeCompleted,
        "duration" -> (timeCompleted - timeStarted)
      )

      val msg = s"Transition '${transition.label}' successfully fired"
      log.logWithMDC(Logging.InfoLevel, msg, mdc)
    }

    def transitionFailed(recipeInstanceId: String,
                         recipeId: String,
                         recipeName: String,
                         transition: Transition,
                         jobId: Long,
                         timeStarted: Long,
                         timeFailed: Long,
                         failureReason: String): Unit = {
      val mdc = Map(
        "processEvent" -> "TransitionFailed",
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "recipeName" -> recipeName,
        "recipeId" -> recipeId,
        "jobId" -> jobId,
        "timeStarted" -> timeStarted,
        "timeFailed" -> timeFailed,
        "duration" -> (timeFailed - timeStarted),
        "transitionId" -> transition.label,
        "failureReason" -> failureReason
      )

      val msg = s"Transition '${transition.label}' failed with: $failureReason"
      log.logWithMDC(Logging.ErrorLevel, msg, mdc)
    }

    def fireTransitionRejected(recipeInstanceId: String,
                               recipeId: String,
                               recipeName: String,
                               transition: Transition,
                               rejectReason: String): Unit = {
      val mdc = Map(
        "processEvent" -> "FireTransitionRejected",
        "recipeInstanceEvent" -> "FireInteractionRejected",
        "recipeName" -> recipeName,
        "recipeId" -> recipeId,
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
        "transitionId" -> transition.label,
        "rejectReason" -> rejectReason)

      val msg = s"Not Firing Transition '${transition.label}' because: $rejectReason"

      log.logWithMDC(Logging.WarningLevel, msg, mdc)
    }

    def idleStop(recipeInstanceId: String, idleTTL: FiniteDuration): Unit = {
      bakerLogging.idleStop(recipeInstanceId, idleTTL)
    }

    def scheduleRetry(recipeInstanceId: String, transition: Transition, delay: Long): Unit = {
      bakerLogging.scheduleRetry(recipeInstanceId, transition, delay)
    }
  }

}
