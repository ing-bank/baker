package com.ing.baker.runtime.catseffect

import cats.effect.{Async, Deferred, IO}
import cats.effect.unsafe.IORuntime

import java.util.concurrent.{CompletableFuture, CompletionException, ExecutionException, ScheduledExecutorService, ScheduledFuture, ScheduledThreadPoolExecutor, TimeUnit}
import java.util.function.{BiConsumer, Function}
import scala.concurrent.duration.FiniteDuration
import scala.util.control.NonFatal

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
  private val scheduler: ScheduledExecutorService = {
    val executor = new ScheduledThreadPoolExecutor(1, (r: Runnable) => {
      val thread = new Thread(r)
      thread.setName("baker-async-support-scheduler")
      thread.setDaemon(true)
      thread
    })
    executor.setRemoveOnCancelPolicy(true)
    executor
  }

  private def failedFuture[A](throwable: Throwable): CompletableFuture[A] = {
    val future = new CompletableFuture[A]()
    future.completeExceptionally(throwable)
    future
  }

  private def unwrap(throwable: Throwable): Throwable = throwable match {
    case completionException: CompletionException if completionException.getCause != null => completionException.getCause
    case executionException: ExecutionException if executionException.getCause != null => executionException.getCause
    case other => other
  }

  private def completeFrom[A](target: CompletableFuture[A], source: CompletableFuture[A]): Unit =
    source.whenComplete(new BiConsumer[A, Throwable] {
      override def accept(value: A, throwable: Throwable): Unit =
        if (throwable == null) target.complete(value)
        else target.completeExceptionally(unwrap(throwable))
    })

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

  implicit val fromCompletableFuture: AsyncSupport[SyncSupport.CompletableFutureF] =
    new AsyncSupport[SyncSupport.CompletableFutureF] {
      override def asyncInstance: Async[CompletableFuture] =
        throw new UnsupportedOperationException("cats Async is not available for CompletableFuture backend")

      override def pure[A](value: A): CompletableFuture[A] = SyncSupport.fromCompletableFuture.pure(value)
      override def map[A, B](fa: CompletableFuture[A])(f: A => B): CompletableFuture[B] = SyncSupport.fromCompletableFuture.map(fa)(f)
      override def flatMap[A, B](fa: CompletableFuture[A])(f: A => CompletableFuture[B]): CompletableFuture[B] = SyncSupport.fromCompletableFuture.flatMap(fa)(f)
      override def raiseError[A](throwable: Throwable): CompletableFuture[A] = SyncSupport.fromCompletableFuture.raiseError(throwable)
      override def delay[A](thunk: => A): CompletableFuture[A] = SyncSupport.fromCompletableFuture.delay(thunk)
      override def blocking[A](thunk: => A): CompletableFuture[A] = SyncSupport.fromCompletableFuture.blocking(thunk)
      override def unit: CompletableFuture[Unit] = SyncSupport.fromCompletableFuture.unit

      override def attempt[A](fa: CompletableFuture[A]): CompletableFuture[Either[Throwable, A]] = {
        val result = new CompletableFuture[Either[Throwable, A]]()
        fa.whenComplete(new BiConsumer[A, Throwable] {
          override def accept(value: A, throwable: Throwable): Unit = {
            val completed =
              if (throwable == null) result.complete(Right(value))
              else result.complete(Left(unwrap(throwable)))
            if (!completed && throwable != null) result.completeExceptionally(unwrap(throwable))
          }
        })
        result
      }

      override def handleErrorWith[A](fa: CompletableFuture[A])(f: Throwable => CompletableFuture[A]): CompletableFuture[A] = {
        val result = new CompletableFuture[A]()
        fa.whenComplete(new BiConsumer[A, Throwable] {
          override def accept(value: A, throwable: Throwable): Unit =
            if (throwable == null) result.complete(value)
            else {
              val recovered: CompletableFuture[A] =
                try f(unwrap(throwable))
                catch {
                  case NonFatal(exception) => failedFuture[A](exception)
                }
              completeFrom(result, recovered)
            }
        })
        result
      }

      override def handleError[A](fa: CompletableFuture[A])(f: Throwable => A): CompletableFuture[A] =
        handleErrorWith(fa)(throwable =>
          try pure(f(throwable))
          catch {
            case NonFatal(exception) => raiseError(exception)
          }
        )

      override def timeoutTo[A](fa: CompletableFuture[A], duration: FiniteDuration, fallback: CompletableFuture[A]): CompletableFuture[A] = {
        val result = new CompletableFuture[A]()
        val timeoutTask: ScheduledFuture[_] = scheduler.schedule(
          new Runnable {
            override def run(): Unit = completeFrom(result, fallback)
          },
          duration.toMillis,
          TimeUnit.MILLISECONDS
        )

        fa.whenComplete(new BiConsumer[A, Throwable] {
          override def accept(value: A, throwable: Throwable): Unit = {
            timeoutTask.cancel(false)
            if (throwable == null) result.complete(value)
            else result.completeExceptionally(unwrap(throwable))
          }
        })
        result
      }

      override def sleep(duration: FiniteDuration): CompletableFuture[Unit] = {
        val result = new CompletableFuture[Unit]()
        scheduler.schedule(
          new Runnable {
            override def run(): Unit = result.complete(())
          },
          duration.toMillis,
          TimeUnit.MILLISECONDS
        )
        result
      }

      override def signal[A]: CompletableFuture[Signal[CompletableFuture, A]] = {
        val gate = new CompletableFuture[A]()
        pure(new Signal[CompletableFuture, A] {
          override def complete(value: A)(implicit async: AsyncSupport[CompletableFuture]): CompletableFuture[Unit] = {
            gate.complete(value)
            async.unit
          }

          override def get(implicit async: AsyncSupport[CompletableFuture]): CompletableFuture[A] = gate
        })
      }

      override def fromCompletableFuture[A](future: CompletableFuture[CompletableFuture[A]]): CompletableFuture[A] =
        future.thenCompose(new Function[CompletableFuture[A], CompletableFuture[A]] {
          override def apply(next: CompletableFuture[A]): CompletableFuture[A] = next
        })

      override def start[A](fa: CompletableFuture[A]): CompletableFuture[CompletableFuture[A]] = pure(fa)

      override def startAndForget[A](fa: CompletableFuture[A]): CompletableFuture[Unit] = {
        fa.whenComplete(new BiConsumer[A, Throwable] {
          override def accept(value: A, throwable: Throwable): Unit = ()
        })
        unit
      }

      override def eager[A](fa: CompletableFuture[A]): CompletableFuture[A] = fa
    }

  def completableFutureSupport: AsyncSupport[SyncSupport.CompletableFutureF] = fromCompletableFuture
}

