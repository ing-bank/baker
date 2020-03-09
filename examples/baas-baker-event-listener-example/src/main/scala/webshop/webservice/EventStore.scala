package webshop.webservice

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO}
import fs2.concurrent.Queue

object EventStore {

  type Enqueue[A] = A => IO[Unit]

  def build[A](implicit cs: ContextShift[IO]): IO[(Enqueue[A], EventStore[A])] =
    for {
      inner <- Ref.of[IO, List[A]](List.empty)
      queue <- Queue.unbounded[IO, A]
      _ <- IO(queue
        .dequeue
        .evalMap(event => inner.update(event :: _))
        .compile
        .drain
        .unsafeRunAsyncAndForget())
    } yield (queue.enqueue1 _, new EventStore(inner))
}

class EventStore[A] private(inner: Ref[IO, List[A]]) {

  def snapshot: IO[List[A]] =
    inner.get
}
