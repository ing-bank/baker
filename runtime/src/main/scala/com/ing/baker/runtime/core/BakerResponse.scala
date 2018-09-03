package com.ing.baker.runtime.core

import java.time.Duration
import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.java_api.EventList

import scala.concurrent.duration.{FiniteDuration, SECONDS}
import scala.concurrent.{Await, ExecutionContext, Future}

object BakerResponse {

  private case class CompletedResponse(sensoryEventStatus: SensoryEventStatus, events: Seq[RuntimeEvent])

  private def firstMessage(processId: String, response: Future[Any])(implicit ec: ExecutionContext): Future[SensoryEventStatus] =
    response.map(translateFirstMessage)

  private def translateFirstMessage(msg: Any): SensoryEventStatus = msg match {
    case ProcessInstanceProtocol.Uninitialized(processId) => throw new NoSuchProcessException(s"No such process: $processId")
    case _: ProcessInstanceProtocol.TransitionFired => SensoryEventStatus.Received
    case _: ProcessInstanceProtocol.TransitionNotEnabled => SensoryEventStatus.FiringLimitMet
    case _: ProcessInstanceProtocol.AlreadyReceived => SensoryEventStatus.AlreadyReceived
    case ProcessIndexProtocol.NoSuchProcess(processId) => throw new NoSuchProcessException(s"No such process: $processId")
    case ProcessIndexProtocol.ReceivePeriodExpired(_) => SensoryEventStatus.ReceivePeriodExpired
    case ProcessIndexProtocol.ProcessDeleted(_) => SensoryEventStatus.ProcessDeleted
    case ProcessIndexProtocol.InvalidEvent(_, invalidEventMessage) => throw new IllegalArgumentException(invalidEventMessage)
    case msg@_ => throw new BakerException(s"Unexpected actor response message: $msg")
  }

  private def allMessages(processId: String, response: Future[Seq[Any]])(implicit ec: ExecutionContext): Future[CompletedResponse] =
    response.map { msgs =>

      val sensoryEventStatus = msgs.headOption.map(translateFirstMessage).map {
        case SensoryEventStatus.Received => SensoryEventStatus.Completed // If the first message is success, then it means we have all the events completed
        case other => other
      }
        .getOrElse(throw new NoSuchProcessException(s"No such process: $processId"))

      val events: Seq[RuntimeEvent] = msgs.flatMap(translateOtherMessage)

      CompletedResponse(sensoryEventStatus, events)
    }

  private def translateOtherMessage(msg: Any): Option[RuntimeEvent] = msg match {
    case fired: ProcessInstanceProtocol.TransitionFired => Option(fired.output.asInstanceOf[RuntimeEvent])
    case _ => None
  }

  private def createFlow(processId: String, source: Source[Any, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext):
                                                              (Future[SensoryEventStatus], Future[CompletedResponse]) = {

    val sinkHead = Sink.head[Any]
    val sinkLast = Sink.seq[Any]

    val graph = RunnableGraph.fromGraph(GraphDSL.create(sinkHead, sinkLast)((_, _)) {
      implicit b =>
        (head, last) => {
          import GraphDSL.Implicits._

          val bcast = b.add(Broadcast[Any](2))
          source ~> bcast.in
          bcast.out(0) ~> head.in
          bcast.out(1) ~> last.in
          ClosedShape
        }
    })

    val (firstResponse, allResponses) = graph.run(materializer)

    (firstMessage(processId, firstResponse), allMessages(processId, allResponses))
  }
}

class BakerResponse(processId: String, source: Source[Any, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext) {

  private val (receivedFuture, completedFuture) = BakerResponse.createFlow(processId, source)

  val defaultWaitTimeout: FiniteDuration = FiniteDuration.apply(10, SECONDS)

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
    new EventList(confirmAllEvents(timeout.toScala))
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
