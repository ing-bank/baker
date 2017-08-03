package com.ing.baker.runtime.core

import java.time.Duration
import java.util.concurrent.{TimeUnit, TimeoutException}

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol.{TransitionFailed, TransitionFired, TransitionNotEnabled, TransitionResponse}

import scala.concurrent.duration.{FiniteDuration, SECONDS}
import scala.concurrent.{Await, ExecutionContext, Future}

object BakerResponse {

  def firstMessage(processId: String, response: Future[Any])(implicit ec: ExecutionContext): Future[Unit] =
    response.flatMap {
      translateFirstMessage
    }.recoverWith {
      // TODO this very hacky
      case e: NoSuchElementException => Future.failed(new NoSuchProcessException(s"No such process: $processId"))
    }

  def translateFirstMessage(msg: Any): Future[Unit] = msg match {
    case t: TransitionFired => Future.successful(())
    case transitionNotEnabled: TransitionNotEnabled =>
      Future.failed(new TransitionNotEnabledException(s"Unexpected actor response message: $transitionNotEnabled"))
    case msg@_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def allMessages(processId: String, response: Future[Seq[Any]])(implicit ec: ExecutionContext): Future[Unit] =
    response.flatMap { msgs =>
      val futureResponses = msgs.headOption.map(translateFirstMessage)
        .getOrElse(Future.failed(new NoSuchProcessException(s"No such process: $processId"))) +: msgs.drop(1).map(translateOtherMessage)
      Future.sequence(futureResponses).map(_ => ())
    }

  def translateOtherMessage(msg: Any): Future[Unit] = msg match {
    case t: TransitionFired => Future.successful(())
    case t: TransitionFailed => Future.successful(())
    case transitionNotEnabled: TransitionNotEnabled =>
      Future.failed(new TransitionNotEnabledException(s"Unexpected actor response message: $transitionNotEnabled"))
    case msg@_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def createFlow(processId: String, source: Source[Any, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext): (Future[Unit], Future[Unit]) = {

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
    try {
      Await.result(receivedFuture, timeout)
      SensoryEventStatus.Received
    }
    catch {
      case _ : TransitionNotEnabledException => SensoryEventStatus.FiringLimitMet
      case e : Exception => throw e
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
    try {
      Await.result(completedFuture, timeout)
      SensoryEventStatus.Completed
    }
    catch {
      case _ : TransitionNotEnabledException => SensoryEventStatus.FiringLimitMet
      case e : Exception => throw e
    }
  }
}
