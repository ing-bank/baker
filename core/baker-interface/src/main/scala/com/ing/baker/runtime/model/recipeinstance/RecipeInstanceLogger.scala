package com.ing.baker.runtime.model.recipeinstance

import com.ing.baker.il.petrinet.Transition
import com.ing.baker.runtime.model.recipeinstance.RecipeInstanceLogger.{Adapter, LogLevel, durationFormatter}
import org.joda.time.format.PeriodFormatter

import scala.concurrent.duration.FiniteDuration

object RecipeInstanceLogger {

  import org.joda.time.format.PeriodFormatterBuilder

  case class Adapter(log: (LogLevel, String, Map[String, String]) => Unit)

  sealed trait LogLevel

  object LogLevel {

    case object Info extends LogLevel

    case object Warn extends LogLevel

    case class Error(throwable: Option[Throwable] = None) extends LogLevel
  }

  val durationFormatter: PeriodFormatter = new PeriodFormatterBuilder()
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
}

case class RecipeInstanceLogger(adapter: Adapter) {

  def processHistoryDeletionSuccessful(recipeInstanceId: String, toSequenceNr: Long) = {
    val msg = s"Process history successfully deleted (up to event sequence $toSequenceNr), stopping the actor"

    val mdc = Map(
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId
    )

    adapter.log(LogLevel.Info, msg, mdc)
  }


  def processHistoryDeletionFailed(recipeInstanceId: String, toSequenceNr: Long, cause: Throwable) = {
    val msg = s"Process events are requested to be deleted up to $toSequenceNr sequence number, but delete operation failed."

    val mdc = Map(
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId
    )

    adapter.log(LogLevel.Error(Some(cause)), msg, mdc)
  }

  def transitionFired(recipeInstanceId: String, transition: Transition, jobId: Long, timeStarted: Long, timeCompleted: Long) = {

    val mdc = Map(
      "processEvent" -> "TransitionFired",
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId,
      "jobId" -> jobId.toString,
      "transitionId" -> transition.label,
      "timeStarted" -> timeStarted.toString,
      "timeCompleted" -> timeCompleted.toString,
      "duration" -> (timeCompleted - timeStarted).toString
    )

    val msg = s"Transition '${transition.label}' successfully fired"
    adapter.log(LogLevel.Info, msg, mdc)
  }

  def transitionFailed(recipeInstanceId: String, transition: Transition, jobId: Long, timeStarted: Long, timeFailed: Long, failureReason: String) {
    val mdc = Map(
      "processEvent" -> "TransitionFailed",
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId,
      "timeStarted" -> timeStarted.toString,
      "timeFailed" -> timeFailed.toString,
      "duration" -> (timeFailed - timeStarted).toString,
      "transitionId" -> transition.label,
      "failureReason" -> failureReason
    )

    val msg = s"Transition '${transition.label}' failed with: $failureReason"
    adapter.log(LogLevel.Error(), msg, mdc)
  }

  def firingInteraction(recipeInstanceId: String, jobId: Long, transition: Transition, timeStarted: Long): Unit = {
    val mdc = Map(
      "processEvent" -> "FiringTransition",
      "recipeInstanceEvent" -> "FiringInteraction",
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId,
      "jobId" -> jobId.toString,
      "transitionId" -> transition.label,
      "timeStarted" -> timeStarted.toString
    )
    val msg = s"Firing interaction ${transition.label}"
    adapter.log(LogLevel.Info, msg, mdc)
  }

  def idleStop(recipeInstanceId: String, idleTTL: FiniteDuration) {
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "processId" -> recipeInstanceId,
    )
    val msg = s"Instance was idle for $idleTTL, stopping the actor"

    adapter.log(LogLevel.Info, msg, mdc)
  }

  def fireTransitionRejected(recipeInstanceId: String, transition: Transition, rejectReason: String) {
    val mdc = Map(
      "processEvent" -> "FireTransitionRejected",
      "recipeInstanceEvent" -> "FireInteractionRejected",
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId,
      "transitionId" -> transition.label,
      "rejectReason" -> rejectReason)

    val msg = s"Not Firing Transition '${transition.label}' because: $rejectReason"

    adapter.log(LogLevel.Warn, msg, mdc)
  }

  def scheduleRetry(recipeInstanceId: String, transition: Transition, delay: Long) {
    val mdc = Map(
      "processEvent" -> "TransitionRetry",
      "recipeInstanceEvent" -> "InteractionRetry",
      "processId" -> recipeInstanceId,
      "recipeInstanceId" -> recipeInstanceId,
      "transitionId" -> transition.label)

    val msg = s"Scheduling a retry of interaction '${transition.label}' in ${durationFormatter.print(new org.joda.time.Period(delay))}"

    adapter.log(LogLevel.Info, msg, mdc)
  }
}
