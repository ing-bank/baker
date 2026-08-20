package com.ing.baker.runtime.catseffect

import cats.effect.{Async, Deferred, IO}
import cats.effect.unsafe.IORuntime

import java.util.concurrent.CompletableFuture
import scala.concurrent.duration.FiniteDuration

/**
  * A one-shot signal that can be completed once and then observed by multiple fibers.
  */
trait Signal[F[_], A] {
  def complete(value: A)(implicit async: AsyncSupport[F]): F[Unit]
  def get(implicit async: AsyncSupport[F]): F[A]
}

/**
  * Minimal asynchronous effect capabilities used by model components.
  */
trait AsyncSupport[F[_]] extends SyncSupport[F] {
  def asyncInstance: Async[F]

  def attempt[A](fa: F[A]): F[Either[Throwable, A]]
  def handleErrorWith[A](fa: F[A])(f: Throwable => F[A]): F[A]
  def handleError[A](fa: F[A])(f: Throwable => A): F[A]
  def timeoutTo[A](fa: F[A], duration: FiniteDuration, fallback: F[A]): F[A]
  def sleep(duration: FiniteDuration): F[Unit]
  def signal[A]: F[Signal[F, A]]
  def fromCompletableFuture[A](future: F[CompletableFuture[A]]): F[A]
  def start[A](fa: F[A]): F[F[A]]
  def startAndForget[A](fa: F[A]): F[Unit]
  def eager[A](fa: F[A]): F[A]
}

object AsyncSupport {
  implicit def toAsync[F[_]](implicit asyncSupport: AsyncSupport[F]): Async[F] =
    asyncSupport.asyncInstance

  implicit def fromIO(implicit runtime: IORuntime = IORuntime.global): AsyncSupport[IO] =
    new AsyncSupport[IO] {
      override def asyncInstance: Async[IO] = IO.asyncForIO

      override def pure[A](value: A): IO[A] = IO.pure(value)
      override def map[A, B](fa: IO[A])(f: A => B): IO[B] = fa.map(f)
      override def flatMap[A, B](fa: IO[A])(f: A => IO[B]): IO[B] = fa.flatMap(f)
      override def raiseError[A](throwable: Throwable): IO[A] = IO.raiseError(throwable)
      override def delay[A](thunk: => A): IO[A] = IO.delay(thunk)
      override def blocking[A](thunk: => A): IO[A] = IO.blocking(thunk)
      override def unit: IO[Unit] = IO.unit

      override def attempt[A](fa: IO[A]): IO[Either[Throwable, A]] = fa.attempt
      override def handleErrorWith[A](fa: IO[A])(f: Throwable => IO[A]): IO[A] = fa.handleErrorWith(f)
      override def handleError[A](fa: IO[A])(f: Throwable => A): IO[A] = fa.handleError(f)
      override def timeoutTo[A](fa: IO[A], duration: FiniteDuration, fallback: IO[A]): IO[A] = fa.timeoutTo(duration, fallback)
      override def sleep(duration: FiniteDuration): IO[Unit] = IO.sleep(duration)
      override def signal[A]: IO[Signal[IO, A]] =
        Deferred[IO, A].flatMap { deferred =>
          IO.pure(new Signal[IO, A] {
            def complete(value: A)(implicit asyncSupport: AsyncSupport[IO]): IO[Unit] =
              deferred.complete(value).map(_ => ())
            def get(implicit asyncSupport: AsyncSupport[IO]): IO[A] =
              deferred.get
          })
        }
      override def fromCompletableFuture[A](future: IO[CompletableFuture[A]]): IO[A] = IO.fromCompletableFuture(future)
      override def start[A](fa: IO[A]): IO[IO[A]] = fa.start.map(_.joinWithNever)
      override def startAndForget[A](fa: IO[A]): IO[Unit] = start(fa).void
      override def eager[A](fa: IO[A]): IO[A] = IO.pure(fa.unsafeRunSync()(runtime))
    }
}

