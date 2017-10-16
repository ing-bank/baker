package com.ing.baker.runtime.core

import java.time.Duration
import java.util.concurrent.{TimeUnit, TimeoutException}

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import com.ing.baker.il.petrinet.Transition
import com.ing.baker.runtime.actor.ProcessInstanceProtocol.{TransitionFailed, TransitionFired, TransitionNotEnabled, TransitionResponse}
import com.ing.baker.runtime.actor.ProcessIndex.ReceivePeriodExpired
import com.ing.baker.runtime.core.InteractionResponse._

import scala.concurrent.duration.{FiniteDuration, SECONDS}
import scala.concurrent.{Await, ExecutionContext, Future}

object InteractionResponse {
  sealed trait InteractionResponse
  case object Success extends InteractionResponse
  case object Failed extends InteractionResponse
  case object NotEnabled extends InteractionResponse
  case object PeriodExpired extends InteractionResponse
}

object BakerResponse {

  def firstMessage(processId: String, response: Future[Any])(implicit ec: ExecutionContext): Future[InteractionResponse] =
    response.flatMap {
      translateFirstMessage
    }.recoverWith {
      // TODO this very hacky
      case e: NoSuchElementException => Future.failed(new NoSuchProcessException(s"No such process: $processId"))
    }

  def translateFirstMessage(msg: Any): Future[InteractionResponse] = msg match {
    case t: TransitionFired => Future.successful(Success)
    case msg: TransitionNotEnabled => Future.successful(NotEnabled)
    case ReceivePeriodExpired => Future.successful(PeriodExpired)
    case msg@_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def allMessages(processId: String, response: Future[Seq[Any]])(implicit ec: ExecutionContext): Future[InteractionResponse] =
    response.flatMap { msgs =>
      val futureResponses = msgs.headOption.map(translateFirstMessage)
        .getOrElse(Future.failed(new NoSuchProcessException(s"No such process: $processId"))) +: msgs.drop(1).map(translateOtherMessage)
      val sequenced = Future.sequence(futureResponses)

      sequenced.map(seq => seq.headOption match {
        case Some(NotEnabled) => NotEnabled
        case Some(PeriodExpired) => PeriodExpired
        case _ => if (seq.exists(_ == Failed)) Failed else Success
      })
    }

  def translateOtherMessage(msg: Any): Future[InteractionResponse] = msg match {
    case t: TransitionFired => Future.successful(Success)
    case t: TransitionFailed => Future.successful(Failed)
    case transitionNotEnabled: TransitionNotEnabled => Future.successful(NotEnabled)
    case msg @_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def createFlow(processId: String, source: Source[Any, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext): (Future[InteractionResponse], Future[InteractionResponse]) = {

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
      case Success => SensoryEventStatus.Received
      case NotEnabled => SensoryEventStatus.FiringLimitMet
      case PeriodExpired => SensoryEventStatus.ReceivePeriodExpired
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
      case Success => SensoryEventStatus.Completed
      case Failed => SensoryEventStatus.Completed
      case NotEnabled => SensoryEventStatus.FiringLimitMet
      case PeriodExpired => SensoryEventStatus.ReceivePeriodExpired
      case _ => throw new BakerException("Unknown exception while handeling sensory event")
    }
  }
}
