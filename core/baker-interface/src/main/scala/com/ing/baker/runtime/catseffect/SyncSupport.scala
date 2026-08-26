package com.ing.baker.runtime.catseffect

import cats.effect.Sync

import java.util.concurrent.{CompletableFuture, CompletionStage, Executor, Executors}
import java.util.function.{Function, Supplier}
import scala.util.control.NonFatal

/**
  * Minimal synchronous effect capabilities used by model components.
  */
trait SyncSupport[F[_]] {
  def pure[A](value: A): F[A]
  def map[A, B](fa: F[A])(f: A => B): F[B]
  def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B]
  def raiseError[A](throwable: Throwable): F[A]
  def delay[A](thunk: => A): F[A]
  def blocking[A](thunk: => A): F[A]
  def unit: F[Unit]
}

object SyncSupport {
  type CompletionStageF[A] = CompletionStage[A]
  type CompletableFutureF[A] = CompletableFuture[A]

  // Dedicated pool for possibly blocking user interaction code.
  private val blockingExecutor: Executor =
    Executors.newCachedThreadPool((r: Runnable) => {
      val thread = new Thread(r)
      thread.setName("baker-sync-support-blocking")
      thread.setDaemon(true)
      thread
    })

  private def failedFuture[A](throwable: Throwable): CompletableFuture[A] = {
    val future = new CompletableFuture[A]()
    future.completeExceptionally(throwable)
    future
  }

  implicit val fromCompletionStage: SyncSupport[CompletionStageF] =
    new SyncSupport[CompletionStageF] {
      override def pure[A](value: A): CompletionStage[A] = CompletableFuture.completedFuture(value)
      override def map[A, B](fa: CompletionStage[A])(f: A => B): CompletionStage[B] =
        fa.thenApply(new Function[A, B] {
          override def apply(value: A): B = f(value)
        })
      override def flatMap[A, B](fa: CompletionStage[A])(f: A => CompletionStage[B]): CompletionStage[B] =
        fa.thenCompose(new Function[A, CompletionStage[B]] {
          override def apply(value: A): CompletionStage[B] = f(value)
        })
      override def raiseError[A](throwable: Throwable): CompletionStage[A] = failedFuture(throwable)
      override def delay[A](thunk: => A): CompletionStage[A] =
        try pure(thunk)
        catch {
          case NonFatal(exception) => raiseError(exception)
        }
      override def blocking[A](thunk: => A): CompletionStage[A] =
        CompletableFuture.supplyAsync(new Supplier[A] {
          override def get(): A = thunk
        }, blockingExecutor)
      override def unit: CompletionStage[Unit] = pure(())
    }

  implicit val fromCompletableFuture: SyncSupport[CompletableFutureF] =
    new SyncSupport[CompletableFutureF] {
      override def pure[A](value: A): CompletableFuture[A] = CompletableFuture.completedFuture(value)
      override def map[A, B](fa: CompletableFuture[A])(f: A => B): CompletableFuture[B] =
        fa.thenApply(new Function[A, B] {
          override def apply(value: A): B = f(value)
        })
      override def flatMap[A, B](fa: CompletableFuture[A])(f: A => CompletableFuture[B]): CompletableFuture[B] =
        fa.thenCompose(new Function[A, CompletableFuture[B]] {
          override def apply(value: A): CompletableFuture[B] = f(value)
        })
      override def raiseError[A](throwable: Throwable): CompletableFuture[A] = failedFuture(throwable)
      override def delay[A](thunk: => A): CompletableFuture[A] =
        try pure(thunk)
        catch {
          case NonFatal(exception) => raiseError(exception)
        }
      override def blocking[A](thunk: => A): CompletableFuture[A] =
        CompletableFuture.supplyAsync(new Supplier[A] {
          override def get(): A = thunk
        }, blockingExecutor)
      override def unit: CompletableFuture[Unit] = pure(())
    }

  object syntax {
    implicit final class SyncEffectOps[F[_], A](private val fa: F[A]) {
      def map[B](f: A => B)(implicit sync: SyncSupport[F]): F[B] =
        sync.map(fa)(f)

      def flatMap[B](f: A => F[B])(implicit sync: SyncSupport[F]): F[B] =
        sync.flatMap(fa)(f)
    }
  }

  implicit def fromSync[F[_]](implicit sync: Sync[F]): SyncSupport[F] =
    new SyncSupport[F] {
      override def pure[A](value: A): F[A] = sync.pure(value)
      override def map[A, B](fa: F[A])(f: A => B): F[B] = sync.map(fa)(f)
      override def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = sync.flatMap(fa)(f)
      override def raiseError[A](throwable: Throwable): F[A] = sync.raiseError(throwable)
      override def delay[A](thunk: => A): F[A] = sync.delay(thunk)
      override def blocking[A](thunk: => A): F[A] = sync.blocking(thunk)
      override def unit: F[Unit] = sync.unit
    }
}

