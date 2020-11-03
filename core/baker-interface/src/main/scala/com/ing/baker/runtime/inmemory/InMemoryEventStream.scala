package com.ing.baker.runtime.inmemory

import cats.implicits._
import cats.effect.IO
import cats.effect.concurrent.Ref
import com.ing.baker.runtime.model.EventStream
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.typesafe.scalalogging.LazyLogging

object InMemoryEventStream {

  def build: IO[InMemoryEventStream] =
    Ref.of[IO, List[BakerEvent => Unit]](List.empty).map(new InMemoryEventStream(_))
}

class InMemoryEventStream(store: Ref[IO, List[BakerEvent => Unit]]) extends EventStream[IO] with LazyLogging {

  override def publish(event: BakerEvent): IO[Unit] =
    for {
      listeners <- store.get
      _ <- listeners.traverse { listener =>
        IO.delay(listener(event)).runAsync {
          case Right(_) => IO.unit
          case Left(e) => IO(logger.error("Exception in event listener", e))
        }.toIO
      }
    } yield ()

  override def subscribe(listenerFunction: BakerEvent => Unit): IO[Unit] =
    store.update(listenerFunction :: _)
}
