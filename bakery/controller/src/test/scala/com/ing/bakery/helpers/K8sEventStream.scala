package com.ing.bakery.helpers

import akka.actor.ActorSystem
import akka.stream.{OverflowStrategy, QueueOfferResult}
import akka.stream.scaladsl.{Source, SourceQueueWithComplete}
import cats.effect.{IO, Resource}
import skuber.ObjectResource
import skuber.api.client.WatchEvent

import scala.concurrent.duration._
import cats.effect.Temporal

object K8sEventStream {

  def resource[O <: ObjectResource](implicit system: ActorSystem, timer: Temporal[IO]): Resource[IO, K8sEventStream[O]] = {
    val q = Source.queue[WatchEvent[O]](bufferSize = 1, overflowStrategy = OverflowStrategy.fail)
    Resource.make(IO(q.preMaterialize()).map { case (queue, source) => new K8sEventStream[O](queue, source) })(_.close)
  }
}

class K8sEventStream[O <: ObjectResource](queue: SourceQueueWithComplete[WatchEvent[O]], _source: Source[WatchEvent[O], _])(implicit cs: ContextShift[IO], timer: Temporal[IO]) {

  def source: Source[WatchEvent[O], _] = _source

  def close: IO[Unit] =
    IO.fromFuture(IO {
      val complete = queue.watchCompletion()
      queue.complete()
      complete
    }).void

  def fire(event: WatchEvent[O]): IO[Unit] = {
    for {
      _ <- IO.sleep(1000.millis)
      _ <- IO.fromFuture(IO(queue.offer(event))).flatMap {
        case QueueOfferResult.Enqueued =>
          IO.unit
        case QueueOfferResult.Dropped =>
          IO.raiseError(new IllegalStateException("K8sEventStream dropped an offered event, try testing one event at a time."))
        case QueueOfferResult.Failure(e) =>
          IO.raiseError(new IllegalStateException("Failure on K8sEventStream event offer...", e))
        case QueueOfferResult.QueueClosed =>
          IO.raiseError(new IllegalStateException("K8sEventStream already closed but an event was still offered."))
      }
      _ <- IO.sleep(1000.millis)
    } yield ()
  }
}
