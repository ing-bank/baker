package com.ing.baker.runtime.common

import cats.effect.Async

import java.util.concurrent.CompletableFuture
import scala.concurrent.duration.FiniteDuration

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
  def fromCompletableFuture[A](future: F[CompletableFuture[A]]): F[A]
  def startAndForget[A](fa: F[A]): F[Unit]
}

object AsyncSupport {
  implicit def toAsync[F[_]](implicit asyncSupport: AsyncSupport[F]): Async[F] =
    asyncSupport.asyncInstance

  implicit def fromAsync[F[_]](implicit async: Async[F]): AsyncSupport[F] =
    new AsyncSupport[F] {
      override def asyncInstance: Async[F] = async

      override def pure[A](value: A): F[A] = async.pure(value)
      override def map[A, B](fa: F[A])(f: A => B): F[B] = async.map(fa)(f)
      override def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = async.flatMap(fa)(f)
      override def raiseError[A](throwable: Throwable): F[A] = async.raiseError(throwable)
      override def delay[A](thunk: => A): F[A] = async.delay(thunk)
      override def blocking[A](thunk: => A): F[A] = async.blocking(thunk)
      override def unit: F[Unit] = async.unit

      override def attempt[A](fa: F[A]): F[Either[Throwable, A]] = async.attempt(fa)
      override def handleErrorWith[A](fa: F[A])(f: Throwable => F[A]): F[A] = async.handleErrorWith(fa)(f)
      override def handleError[A](fa: F[A])(f: Throwable => A): F[A] = async.handleError(fa)(f)
      override def timeoutTo[A](fa: F[A], duration: FiniteDuration, fallback: F[A]): F[A] = async.timeoutTo(fa, duration, fallback)
      override def sleep(duration: FiniteDuration): F[Unit] = async.sleep(duration)
      override def fromCompletableFuture[A](future: F[CompletableFuture[A]]): F[A] = async.fromCompletableFuture(future)
      override def startAndForget[A](fa: F[A]): F[Unit] = async.map(async.start(fa))(_ => ())
    }
}

