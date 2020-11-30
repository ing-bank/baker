package com.ing.baker.runtime.model

import cats.effect.Sync
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.Transition
import com.ing.baker.runtime.scaladsl.EventInstance
import com.typesafe.scalalogging.Logger
import org.joda.time.Period
import org.joda.time.format.{PeriodFormatter, PeriodFormatterBuilder}
import org.slf4j.MDC

import scala.concurrent.duration.FiniteDuration

object BakerLogging {

  lazy val defaultLogger: Logger = Logger("com.ing.baker")
}

case class BakerLogging(logger: Logger = BakerLogging.defaultLogger) {

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

  private def withMDC[F[_]](mdc: Map[String, String], log: Logger => Unit)(implicit effect: Sync[F]): F[Unit] =
    effect.delay {
      mdc.foreach { case (k, v) => MDC.put(k, v) }
      log(logger)
      mdc.keys.foreach(MDC.remove)
    }

  def addedRecipe[F[_]](recipe: CompiledRecipe, timestamp: Long)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Added recipe '${recipe.name}'"
    val MDC = Map(
      "recipeName" -> recipe.name,
      "recipeId" -> recipe.recipeId,
      "addedOn" -> timestamp.toString
    )
    withMDC(MDC, _.info(msg))
  }

  def recipeInstanceCreated[F[_]](recipeInstanceId: String, createdOn: Long, recipe: CompiledRecipe)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Baked recipe instance '$recipeInstanceId' from recipe '${recipe.name}'"
    val MDC = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "createdOn" -> createdOn.toString,
      "recipeName" -> recipe.name,
      "recipeId" -> recipe.recipeId
    )
    withMDC(MDC, _.info(msg))
  }

  def firingEvent[F[_]](recipeInstanceId: String, executionId: Long, transition: Transition, timeStarted: Long)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Firing event '${transition.label}'"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "eventName" -> transition.label,
      "runtimeTimestamp" -> timeStarted.toString,
      "executionId" -> executionId.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def interactionStarted[F[_]](recipeInstanceId: String, executionId: Long, transition: Transition, timeStarted: Long)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Interaction started '${transition.label}'"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "interactionName" -> transition.label,
      "timeStarted" -> timeStarted.toString,
      "executionId" -> executionId.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def interactionFinished[F[_]](recipeInstanceId: String, executionId: Long, transition: Transition, timeStarted: Long, timeFinished: Long)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Interaction finished '${transition.label}'"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "interactionName" -> transition.label,
      "duration" -> (timeFinished - timeStarted).toString,
      "timeStarted" -> timeStarted.toString,
      "timeFinished" -> timeFinished.toString,
      "executionId" -> executionId.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def interactionFailed[F[_]](recipeInstanceId: String, transition: Transition, executionId: Long, timeStarted: Long, timeFailed: Long, failureReason: Throwable)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Interaction failed '${transition.label}'"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "interactionName" -> transition.label,
      "duration" -> (timeFailed - timeStarted).toString,
      "timeStarted" -> timeStarted.toString,
      "timeFailed" -> timeFailed.toString,
      "executionId" -> executionId.toString,
    )
    withMDC(mdc, _.error(msg, failureReason))
  }

  def idleStop[F[_]](recipeInstanceId: String, idleTTL: FiniteDuration)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Instance was idle for $idleTTL"
    val mdc = Map("recipeInstanceId" -> recipeInstanceId)
    withMDC(mdc, _.info(msg))
  }

  def eventRejected[F[_]](recipeInstanceId: String, event: EventInstance, rejectReason: String)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Event rejected '${event.name}' because: $rejectReason"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "event" -> event.name,
      "rejectReason" -> rejectReason
    )
    withMDC(mdc, _.warn(msg))
  }

  def scheduleRetry[F[_]](recipeInstanceId: String, transition: Transition, delay: Long)(implicit effect: Sync[F]): F[Unit] = {
    val msg = s"Scheduling a retry of interaction '${transition.label}' in ${durationFormatter.print(new Period(delay))}"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "interactionName" -> transition.label,
      "delay" -> delay.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def exceptionOnEventListener[F[_]](throwable: Throwable)(implicit effect: Sync[F]): F[Unit] =
    effect.delay(logger.error("Exception on event listener", throwable))
}
