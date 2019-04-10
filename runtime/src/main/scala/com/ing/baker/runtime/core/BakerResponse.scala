package com.ing.baker.runtime.core

import java.time.Duration
import java.util.concurrent.{CompletableFuture, TimeoutException}

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import com.ing.baker.runtime.java_api.EventList

import scala.compat.java8.FutureConverters
import scala.concurrent.duration.{FiniteDuration, SECONDS}
import scala.concurrent.{Await, ExecutionContext, Future}

object BakerResponse {

  case class CompletedResponse(sensoryEventStatus: SensoryEventStatus, events: Seq[RuntimeEvent])

  private def firstMessage(processId: String, response: Future[BakerResponseEventProtocol])(implicit ec: ExecutionContext): Future[SensoryEventStatus] =
    response.map(_.toSensoryEventStatus)

  private def allMessages(processId: String, response: Future[Seq[BakerResponseEventProtocol]])(implicit ec: ExecutionContext): Future[CompletedResponse] =
    response.map { msgs =>

      val sensoryEventStatus = msgs.headOption.map(_.toSensoryEventStatus).map {
        case SensoryEventStatus.Received => SensoryEventStatus.Completed // If the first message is success, then it means we have all the events completed
        case other => other
      }
        .getOrElse(throw new NoSuchProcessException(s"No such process: $processId"))

      val events: Seq[RuntimeEvent] = msgs.flatMap(translateOtherMessage)

      CompletedResponse(sensoryEventStatus, events)
    }

  private def translateOtherMessage(msg: BakerResponseEventProtocol): Option[RuntimeEvent] = msg match {
    case BakerResponseEventProtocol.InstanceTransitionFired(value) =>
      Option(value.output.asInstanceOf[RuntimeEvent])
    case _ =>
      None
  }

  private def createFlow(processId: String, futureSource: Future[Source[BakerResponseEventProtocol, NotUsed]])(implicit materializer: Materializer, ec: ExecutionContext):
   Future[(Future[SensoryEventStatus], Future[CompletedResponse])] = {

    def graph(source: Source[BakerResponseEventProtocol, NotUsed]) =
      RunnableGraph.fromGraph(GraphDSL.create(Sink.head[BakerResponseEventProtocol], Sink.seq[BakerResponseEventProtocol], source)((s1, s2, _) => (s1, s2)) {
        implicit b =>
          (head, last, source0) => {
            import GraphDSL.Implicits._

            val bcast = b.add(Broadcast[BakerResponseEventProtocol](2))
            source0 ~> bcast.in
            bcast.out(0) ~> head.in
            bcast.out(1) ~> last.in
            ClosedShape
          }
      })

    futureSource.map(graph(_).run(materializer)).map { case (firstResponse, allResponses) =>
      (firstMessage(processId, firstResponse), allMessages(processId, allResponses))
    }

  }
}

class BakerResponse(processId: String, futureSource: Future[Source[BakerResponseEventProtocol, NotUsed]])(implicit materializer: Materializer, ec: ExecutionContext) {

  //val (receivedFuture, completedFuture) = BakerResponse.createFlow(processId, futureSource)
  private val futureEvents = BakerResponse.createFlow(processId, futureSource)

  val receivedFuture: Future[SensoryEventStatus] = futureEvents.flatMap(_._1)

  val completedFuture: Future[BakerResponse.CompletedResponse] = futureEvents.flatMap(_._2)

  val defaultWaitTimeout: FiniteDuration = FiniteDuration.apply(10, SECONDS)

  def completedFutureJava: CompletableFuture[BakerResponse.CompletedResponse] =
    FutureConverters.toJava(completedFuture).toCompletableFuture

  def receivedFutureJava: CompletableFuture[SensoryEventStatus] =
    FutureConverters.toJava(receivedFuture).toCompletableFuture

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmReceived(): SensoryEventStatus = {
    confirmReceived(defaultWaitTimeout)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmReceived(duration: Duration): SensoryEventStatus = {
    confirmReceived(duration.toScala)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmReceived(implicit timeout: FiniteDuration): SensoryEventStatus = {
    Await.result(receivedFuture, timeout)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmCompleted(): SensoryEventStatus = {
    confirmCompleted(defaultWaitTimeout)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmCompleted(duration: Duration): SensoryEventStatus = {
    confirmCompleted(duration.toScala)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmCompleted(implicit timeout: FiniteDuration): SensoryEventStatus = {
    Await.result(completedFuture, timeout).sensoryEventStatus
  }

  /**
    * Waits for all events that where caused by the sensory event input.
    *
    * !!! Note that this will return an empty list if the sensory event was rejected
    *
    * Therefor you are encouraged to first confirm that the event was properly received before checking this list.
    * {{{
    * BakerResponse response = baker.processEvent(someEvent);
    *
    * switch (response.confirmReceived()) {
    *   case Received:
    *
    *     EventList events = response.confirmAllEvents()
    *     // ...
    *     break;
    *
    *   case ReceivePeriodExpired:
    *   case AlreadyReceived:
    *   case ProcessDeleted:
    *   case FiringLimitMet:
    *   case AlreadyReceived:
    *     // ...
    *     break;
    * }
    * }}}
    * @param timeout The duration to wait for completion
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmAllEvents(timeout: Duration): EventList = {
    EventList.ScalaWithNoTimestamps(confirmAllEvents(timeout.toScala))
  }

  /**
    * Waits for all events that where caused by the sensory event input.
    *
    * !!! Note that this will return an empty list if the sensory event was rejected
    *
    * Therefor you are encouraged to first confirm that the event was properly received before checking this list.
    *
    * Example:
    *
    * {{{
    * val response = baker.processEvent(someEvent);
    *
    * response.confirmReceived() match {
    *   case Received =>
    *
    *     response.confirmAllEvents()
    *
    *   case ReceivePeriodExpired =>
    *   case AlreadyReceived =>
    *   case ProcessDeleted =>
    *   case FiringLimitMet =>
    *   case AlreadyReceived =>
    * }
    * }}}
    *
    * @param timeout The duration to wait for completion
    * @return
    */
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmAllEvents(implicit timeout: FiniteDuration): Seq[RuntimeEvent] = {
    Await.result(completedFuture, timeout).events
  }
}
