package com.ing.baker.runtime.core

import java.time.Duration
import java.util.concurrent.TimeUnit

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol.{TransitionFailed, TransitionFired, TransitionNotEnabled, TransitionResponse}
import com.ing.baker.runtime.core.SensoryEventStatus.SensoryEventStatus

import scala.concurrent.duration.{FiniteDuration, SECONDS}
import scala.concurrent.{Await, ExecutionContext, Future}

object BakerResponse {

  def firstMessage(processId: String, response: Future[TransitionResponse])(implicit ec: ExecutionContext): Future[Unit] =
    response.flatMap {
      translateFirstMessage
    }.recoverWith {
      // TODO this very hacky
      case e: NoSuchElementException => Future.failed(new NoSuchProcessException(s"No such process: $processId"))
    }

  def translateFirstMessage(msg: TransitionResponse): Future[Unit] = msg match {
    case t: TransitionFired => Future.successful(())
    case transitionNotEnabled: TransitionNotEnabled =>
      Future.failed(new TransitionNotEnabledException(s"Unexpected actor response message: $transitionNotEnabled"))
    case msg@_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def allMessages(processId: String, response: Future[Seq[TransitionResponse]])(implicit ec: ExecutionContext): Future[Unit] =
    response.flatMap { msgs =>
      val futureResponses = msgs.headOption.map(translateFirstMessage)
        .getOrElse(Future.failed(new NoSuchProcessException(s"No such process: $processId"))) +: msgs.drop(1).map(translateOtherMessage)
      Future.sequence(futureResponses).map(_ => ())
    }

  def translateOtherMessage(msg: TransitionResponse): Future[Unit] = msg match {
    case t: TransitionFired => Future.successful(())
    case t: TransitionFailed => Future.successful(())
    case transitionNotEnabled: TransitionNotEnabled =>
      Future.failed(new TransitionNotEnabledException(s"Unexpected actor response message: $transitionNotEnabled"))
    case msg@_ => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def createFlow(processId: String, source: Source[TransitionResponse, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext): (Future[Unit], Future[Unit]) = {

    val sinkHead = Sink.head[TransitionResponse]
    val sinkLast = Sink.seq[TransitionResponse]

    val graph = RunnableGraph.fromGraph(GraphDSL.create(sinkHead, sinkLast)((_, _)) {
      implicit b =>
        (head, last) => {
          import GraphDSL.Implicits._

          val bcast = b.add(Broadcast[TransitionResponse](2))
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

class BakerResponse(processId: String, source: Source[TransitionResponse, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext) {

  val (receivedFuture, completedFuture) = BakerResponse.createFlow(processId, source)

  val defaultWaitTimeout: FiniteDuration = FiniteDuration.apply(10, SECONDS)

  def confirmReceived(): SensoryEventStatus = {
    confirmReceived(defaultWaitTimeout)
  }

  def confirmReceived(duration: Duration): SensoryEventStatus = {
    confirmReceived(FiniteDuration(duration.toNanos, TimeUnit.NANOSECONDS))
  }

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

  def confirmCompleted(): SensoryEventStatus = {
    confirmCompleted(defaultWaitTimeout)
  }

  def confirmCompleted(duration: Duration): SensoryEventStatus = {
    confirmCompleted(FiniteDuration(duration.toNanos, TimeUnit.NANOSECONDS))
  }

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
