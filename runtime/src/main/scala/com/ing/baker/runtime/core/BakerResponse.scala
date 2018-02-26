package com.ing.baker.runtime.core

import java.time.Duration
import java.util.concurrent.{TimeUnit, TimeoutException}

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.core.InteractionResponse._

import scala.concurrent.duration.{FiniteDuration, SECONDS}
import scala.concurrent.{Await, ExecutionContext, Future}

object InteractionResponse {

  sealed trait InteractionResponse

  case object Success extends InteractionResponse
  case object Failed extends InteractionResponse
  case object NotEnabled extends InteractionResponse
  case object PeriodExpired extends InteractionResponse
  case object ProcessDeleted extends InteractionResponse
  case object AlreadyReceived extends InteractionResponse
}

object BakerResponse {

  private def firstMessage(processId: String, response: Future[Any])(implicit ec: ExecutionContext): Future[InteractionResponse] =
    response.flatMap(translateFirstMessage)

  private def translateFirstMessage(msg: Any): Future[InteractionResponse] = msg match {
    case ProcessInstanceProtocol.Uninitialized(processId) => Future.failed(new NoSuchProcessException(s"No such process: $processId"))
    case _: ProcessInstanceProtocol.TransitionFired => Future.successful(InteractionResponse.Success)
    case _: ProcessInstanceProtocol.TransitionNotEnabled => Future.successful(InteractionResponse.NotEnabled)
    case _: ProcessInstanceProtocol.AlreadyReceived => Future.successful(InteractionResponse.AlreadyReceived)
    case ProcessIndexProtocol.ProcessUninitialized(processId) => Future.failed(new NoSuchProcessException(s"No such process: $processId"))
    case ProcessIndexProtocol.ReceivePeriodExpired(_) => Future.successful(InteractionResponse.PeriodExpired)
    case ProcessIndexProtocol.ProcessDeleted(_) => Future.successful(InteractionResponse.ProcessDeleted)
    case ProcessIndexProtocol.InvalidEvent(_, invalidEventMessage) => Future.failed(new IllegalArgumentException(invalidEventMessage))
    case msg@_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  private def allMessages(processId: String, response: Future[Seq[Any]])(implicit ec: ExecutionContext): Future[InteractionResponse] =
    response.flatMap { msgs =>
      val futureResponses = msgs.headOption.map(translateFirstMessage)
        .getOrElse(Future.failed(new NoSuchProcessException(s"No such process: $processId"))) +: msgs.drop(1).map(translateOtherMessage)
      val sequenced = Future.sequence(futureResponses)

      sequenced.map(seq => seq.headOption match {
        case Some(NotEnabled) => NotEnabled
        case Some(PeriodExpired) => PeriodExpired
        case Some(AlreadyReceived) => AlreadyReceived
        case _ => if (seq.contains(Failed)) Failed else Success
      })
    }

  private def translateOtherMessage(msg: Any): Future[InteractionResponse] = msg match {
    case _: ProcessInstanceProtocol.TransitionFired => Future.successful(Success)
    case _: ProcessInstanceProtocol.TransitionFailed => Future.successful(Failed)
    case _: ProcessInstanceProtocol.TransitionNotEnabled => Future.successful(NotEnabled)
    case msg @_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  private def createFlow(processId: String, source: Source[Any, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext): (Future[InteractionResponse], Future[InteractionResponse]) = {

    val sinkHead = Sink.head[Any]
    val sinkLast = Sink.seq[Any]

    Sink.queue()

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

  val (receivedFuture, completedFuture) = BakerResponse.createFlow(processId, source)

  val defaultWaitTimeout: FiniteDuration = FiniteDuration.apply(10, SECONDS)

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmReceived(): SensoryEventStatus = {
    confirmReceived(defaultWaitTimeout)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmReceived(duration: Duration): SensoryEventStatus = {
    confirmReceived(FiniteDuration(duration.toNanos, TimeUnit.NANOSECONDS))
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmReceived(implicit timeout: FiniteDuration): SensoryEventStatus = {

    val result = Await.result(receivedFuture, timeout)

    result match {
      case InteractionResponse.Success => SensoryEventStatus.Received
      case InteractionResponse.NotEnabled => SensoryEventStatus.FiringLimitMet
      case InteractionResponse.PeriodExpired => SensoryEventStatus.ReceivePeriodExpired
      case InteractionResponse.AlreadyReceived => SensoryEventStatus.AlreadyReceived
      case InteractionResponse.ProcessDeleted => SensoryEventStatus.ProcessDeleted
      case _ => throw new BakerException("Unknown exception while handeling sensory event")
    }
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmCompleted(): SensoryEventStatus = {
    confirmCompleted(defaultWaitTimeout)
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmCompleted(duration: Duration): SensoryEventStatus = {
    confirmCompleted(FiniteDuration(duration.toNanos, TimeUnit.NANOSECONDS))
  }

  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def confirmCompleted(implicit timeout: FiniteDuration): SensoryEventStatus = {

    val result = Await.result(completedFuture, timeout)

    result match {
      case InteractionResponse.Success => SensoryEventStatus.Completed
      case InteractionResponse.Failed => SensoryEventStatus.Completed
      case InteractionResponse.NotEnabled => SensoryEventStatus.FiringLimitMet
      case InteractionResponse.PeriodExpired => SensoryEventStatus.ReceivePeriodExpired
      case InteractionResponse.AlreadyReceived => SensoryEventStatus.AlreadyReceived
      case InteractionResponse.ProcessDeleted => SensoryEventStatus.ProcessDeleted
      case _ => throw new BakerException("Unknown exception while handling sensory event")
    }
  }
}
