package com.ing.baker.runtime.model

import com.ing.baker.il.petrinet.Transition
import com.ing.baker.runtime.common._
import com.typesafe.scalalogging.Logger
import org.joda.time.Period
import org.joda.time.format.{PeriodFormatter, PeriodFormatterBuilder}
import org.slf4j.MDC

import scala.concurrent.duration.FiniteDuration

object BakerLogging {
  lazy val defaultLogger: Logger = Logger("com.ing.baker")

  lazy val default: BakerLogging = BakerLogging()
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

  private def withMDC(mdc: Map[String, String], log: Logger => Unit): Unit = {
      mdc.foreach { case (k, v) => MDC.put(k, v) }
      log(logger)
      mdc.keys.foreach(MDC.remove)
    }

  def addedRecipe(recipeAdded: RecipeAdded): Unit = {
    val msg = s"Added recipe '${recipeAdded.recipeName}'"
    val MDC = Map(
      "recipeName" -> recipeAdded.recipeName,
      "recipeId" -> recipeAdded.recipeId,
      "addedOn" -> recipeAdded.date.toString
    )
    withMDC(MDC, _.info(msg))
  }

  def recipeInstanceCreated(recipeInstanceCreated: RecipeInstanceCreated): Unit = {
    val msg = s"Baked recipe instance '${recipeInstanceCreated.recipeInstanceId}' from recipe '${recipeInstanceCreated.recipeName} : ${recipeInstanceCreated.recipeId}'"
    val MDC = Map(
      "recipeInstanceId" -> recipeInstanceCreated.recipeInstanceId,
      "createdOn" -> recipeInstanceCreated.timeStamp.toString,
      "recipeName" -> recipeInstanceCreated.recipeName,
      "recipeId" -> recipeInstanceCreated.recipeId
    )
    withMDC(MDC, _.info(msg))
  }

  def interactionStarted(interactionStarted: InteractionStarted): Unit = {
    val msg = s"Interaction started '${interactionStarted.interactionName}'"
    val mdc = Map(
      "recipeInstanceId" -> interactionStarted.recipeInstanceId,
      "interactionName" -> interactionStarted.interactionName,
      "timeStarted" -> interactionStarted.timeStamp.toString,
      "recipeId" -> interactionStarted.recipeId,
      "recipeName" -> interactionStarted.recipeName
    )
    withMDC(mdc, _.info(msg))
  }

  def interactionFinished(interactionCompleted: InteractionCompleted): Unit = {
    val msg = s"Interaction finished '${interactionCompleted.interactionName}'"
    val mdc = Map(
      "recipeInstanceId" -> interactionCompleted.recipeInstanceId,
      "interactionName" -> interactionCompleted.interactionName,
      "duration" -> interactionCompleted.duration.toString,
      "timeFinished" -> interactionCompleted.timeStamp.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def interactionFailed(interactionFailed: InteractionFailed): Unit = {
    val msg = s"Interaction failed '${interactionFailed.interactionName}'"
    val mdc = Map(
      "recipeInstanceId" -> interactionFailed.recipeInstanceId,
      "interactionName" -> interactionFailed.interactionName,
      "duration" -> interactionFailed.duration.toString,
      "timeFailed" -> interactionFailed.timeStamp.toString,
      "recipeId" -> interactionFailed.recipeId,
      "recipeName" -> interactionFailed.recipeName,
      "failureCount" -> interactionFailed.failureCount.toString
    )
    withMDC(mdc, _.error(msg, interactionFailed.throwable))
  }

  def firingEvent(recipeInstanceId: String, executionId: Long, transition: Transition, timeStarted: Long): Unit = {
    val msg = s"Firing event '${transition.label}'"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "eventName" -> transition.label,
      "runtimeTimestamp" -> timeStarted.toString,
      "executionId" -> executionId.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def eventReceived(eventReceived: EventReceived): Unit = {
    val msg = s"Event received '${eventReceived.event.name}'"
    val mdc = Map(
      "event" -> eventReceived.event.name,
      "recipeInstanceId" -> eventReceived.recipeInstanceId,
      "recipeId" -> eventReceived.recipeId,
      "recipeName" -> eventReceived.recipeName,
      "timeReceived" -> eventReceived.timeStamp.toString,
    )
    withMDC(mdc, _.warn(msg))
  }

  def eventRejected(eventRejected: EventRejected): Unit = {
    val msg = s"Event rejected '${eventRejected.event.name}' because: ${eventRejected.reason}"
    val mdc = Map(
      "event" -> eventRejected.event.name,
      "recipeInstanceId" -> eventRejected.recipeInstanceId,
      "timeReceived" -> eventRejected.timeStamp.toString,
    )
    withMDC(mdc, _.warn(msg))
  }

  def scheduleRetry(recipeInstanceId: String, transition: Transition, delay: Long): Unit = {
    val msg = s"Scheduling a retry of interaction '${transition.label}' in ${durationFormatter.print(new Period(delay))}"
    val mdc = Map(
      "recipeInstanceId" -> recipeInstanceId,
      "interactionName" -> transition.label,
      "delay" -> delay.toString
    )
    withMDC(mdc, _.info(msg))
  }

  def idleStop(recipeInstanceId: String, idleTTL: FiniteDuration): Unit = {
    val msg = s"Instance was idle for $idleTTL"
    val mdc = Map("recipeInstanceId" -> recipeInstanceId)
    withMDC(mdc, _.info(msg))
  }

  def exceptionOnEventListener(throwable: Throwable): Unit =
    logger.error("Exception on event listener", throwable)
}
