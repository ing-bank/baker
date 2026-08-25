package com.ing.baker.runtime.catseffect

import cats.effect.Sync
import cats.effect.kernel.Ref

import java.util.concurrent.CompletableFuture
import java.util.concurrent.atomic.AtomicReference

/**
  * Minimal Ref allocation capability used by model components.
  */
trait RefState[F[_], A] {
  def get: F[A]
  def update(f: A => A): F[Unit]
  def modify[B](f: A => (A, B)): F[B]
}

trait RefSupport[F[_]] {
  def of[A](value: A): F[RefState[F, A]]
}

object RefSupport {

  private final case class CatsRefState[F[_], A](ref: Ref[F, A]) extends RefState[F, A] {
    override def get: F[A] = ref.get
    override def update(f: A => A): F[Unit] = ref.update(f)
    override def modify[B](f: A => (A, B)): F[B] = ref.modify(f)
  }

  private final class CompletableFutureRefState[A](initial: A) extends RefState[SyncSupport.CompletableFutureF, A] {
    private val state = new AtomicReference[A](initial)

    override def get: CompletableFuture[A] = CompletableFuture.completedFuture(state.get())

    override def update(f: A => A): CompletableFuture[Unit] = {
      state.updateAndGet(value => f(value))
      CompletableFuture.completedFuture(())
    }

    override def modify[B](f: A => (A, B)): CompletableFuture[B] = this.synchronized {
      val (next, out) = f(state.get())
      state.set(next)
      CompletableFuture.completedFuture(out)
    }
  }

  implicit def fromSync[F[_]](implicit sync: Sync[F]): RefSupport[F] =
    new RefSupport[F] {
      override def of[A](value: A): F[RefState[F, A]] =
        sync.map(Ref.of[F, A](value))(CatsRefState(_))
    }

  implicit def fromAsyncSupport[F[_]](implicit async: AsyncSupport[F]): RefSupport[F] =
    async match {
      case _: AsyncSupport[SyncSupport.CompletableFutureF] =>
        fromCompletableFuture.asInstanceOf[RefSupport[F]]
      case _ =>
        fromSync(async.asyncInstance)
    }

  implicit val fromCompletableFuture: RefSupport[SyncSupport.CompletableFutureF] =
    new RefSupport[SyncSupport.CompletableFutureF] {
      override def of[A](value: A): CompletableFuture[RefState[SyncSupport.CompletableFutureF, A]] =
        CompletableFuture.completedFuture(new CompletableFutureRefState[A](value))
    }
}

