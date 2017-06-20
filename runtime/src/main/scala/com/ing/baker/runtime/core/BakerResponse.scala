package com.ing.baker.runtime.core

import java.util.UUID

import akka.NotUsed
import akka.stream.javadsl.RunnableGraph
import akka.stream.scaladsl.{Broadcast, GraphDSL, Sink, Source}
import akka.stream.{ClosedShape, Materializer}
import io.kagera.akka.actor.PetriNetInstanceProtocol.{TransitionFailed, TransitionFired, TransitionResponse}

import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, ExecutionContext, Future}

object BakerResponse {

  def firstMessage(processId: java.util.UUID, response: Future[TransitionResponse])(implicit ec: ExecutionContext): Future[Unit] =
    response.flatMap { translateFirstMessage }.recoverWith {
      // TODO this very hacky
      case e: NoSuchElementException => Future.failed(new NoSuchProcessException(s"No such process: $processId"))
    }

  def translateFirstMessage(msg: TransitionResponse): Future[Unit] = msg match {
    case t: TransitionFired      => Future.successful(())
    case msg @ _                 => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def allMessages(processId: java.util.UUID, response: Future[Seq[TransitionResponse]])(implicit ec: ExecutionContext): Future[Unit] =
    response.flatMap { msgs =>
        val futureResponses = msgs.headOption.map(translateFirstMessage)
          .getOrElse(Future.failed(new NoSuchProcessException(s"No such process: $processId"))) +: msgs.drop(1).map(translateOtherMessage)
        Future.sequence(futureResponses).map( _ =>())
    }

  def translateOtherMessage(msg: TransitionResponse): Future[Unit] = msg match {
    case t: TransitionFired      => Future.successful(())
    case t: TransitionFailed     => Future.successful(())
    case msg @ _                 => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
  }

  def createFlow(processId: java.util.UUID, source: Source[TransitionResponse, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext): (Future[Unit], Future[Unit]) = {

    val sinkHead = Sink.head[TransitionResponse]
    val sinkLast = Sink.seq[TransitionResponse]

    val graph = RunnableGraph.fromGraph(GraphDSL.create(sinkHead, sinkLast)((_, _)) {
      implicit b => (head, last) => {
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

class BakerResponse(processId: UUID, source: Source[TransitionResponse, NotUsed])(implicit materializer: Materializer, ec: ExecutionContext) {

  val (receivedFuture, completedFuture) = BakerResponse.createFlow(processId, source)

  def confirmReceived(implicit timeout: FiniteDuration): Unit = Await.result(receivedFuture, timeout)

  def confirmCompleted(implicit timeout: FiniteDuration): Unit = Await.result(completedFuture, timeout)

}
