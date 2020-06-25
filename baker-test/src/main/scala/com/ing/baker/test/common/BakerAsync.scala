package com.ing.baker.test.common

import java.util.concurrent.{CountDownLatch, TimeUnit}

import com.ing.baker.runtime.common.EventInstance
import com.ing.baker.runtime.scaladsl.{Baker, RecipeEventMetadata}
import com.ing.baker.test.scaladsl.BakerEventsFlow
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.language.postfixOps
import scala.util.{Failure, Success}

class BakerAsync(baker: Baker, duration: Duration = 10 seconds) extends LazyLogging {

  private case class EventMessage(recipeInstanceId: String, eventName: String)

  private val queue = new AsyncMessages[EventMessage]
  private val waitForOnboarding = new CountDownLatch(1)

  private def isEventRegistered(recipeInstanceId: String, eventInstance: EventInstance): Boolean =
    Await.result(baker.getEventNames(recipeInstanceId), duration).contains(eventInstance.name)

  baker.registerEventListener((recipeEventMetadata: RecipeEventMetadata, event: EventInstance) => {
    waitForOnboarding.await(duration.toMillis, TimeUnit.MILLISECONDS)
    logger.debug("Event {} is received for processId {}", event.asInstanceOf[Any], recipeEventMetadata.asInstanceOf[Any])
    while (!isEventRegistered(recipeEventMetadata.recipeInstanceId, event)) {
      logger.trace("Event {} is not yet visible in baker, waiting for 10 millis ...", event.name)
      Thread.sleep(10)
    }
    logger.trace("Adding event {} to the queue", event.name)
    queue.put(EventMessage(recipeEventMetadata.recipeInstanceId, event.name))
  })

  private def getRecipeInstanceIds: Future[Set[String]] =
    baker.getAllRecipeInstancesMetadata.map(_.map(_.recipeInstanceId))

  private def getEventMessages(recipeInstanceId: String): Future[Seq[EventMessage]] =
    baker.getEventNames(recipeInstanceId)
      .map(eventNames => eventNames.map(name => EventMessage(recipeInstanceId, name)))

  private val eventNames: Future[Set[EventMessage]] = for {
    recipeInstanceIds <- getRecipeInstanceIds
    eventNames <- Future.sequence(recipeInstanceIds.map(getEventMessages))
  } yield eventNames.flatten

  eventNames.onComplete {
    case Success(events) =>
      events.foreach(queue.put)
      waitForOnboarding.countDown() // start accepting new events
    case Failure(exception) => exception.printStackTrace()
  }

  private def createPredicate(recipeInstanceId: String, eventName: String): EventMessage => Boolean = {
    val eventMessage = EventMessage(recipeInstanceId, eventName)
    msg => eventMessage == msg
  }

  private def createPredicates(recipeInstanceId: String, flow: BakerEventsFlow): Seq[EventMessage => Boolean] =
    flow.events.map(createPredicate(recipeInstanceId, _)).toSeq

  def waitFor(recipeInstanceId: String, flow: BakerEventsFlow): Unit = {
    val predicates = createPredicates(recipeInstanceId, flow)
    Await.result(queue.get(predicates: _*), duration)
  }
}
