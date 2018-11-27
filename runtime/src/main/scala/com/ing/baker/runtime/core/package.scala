package com.ing.baker.runtime

import java.lang.Thread.UncaughtExceptionHandler
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.{Executors, ThreadFactory, TimeUnit}

import cats.effect.IO

import scala.concurrent.ExecutionContext
import scala.concurrent.duration.FiniteDuration
import scala.util.control.NonFatal

package object core {

  implicit class IOHandleErrors[T](io: IO[T]) {

    def handleException[Y >: T](pf: PartialFunction[Throwable, Y]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).map(IO.pure(_)).getOrElse(IO.raiseError(throwable))
      }

    def handleExceptionWith[Y >: T](pf: PartialFunction[Throwable, IO[Y]]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).getOrElse(IO.raiseError(throwable))
      }
  }

  implicit class JavaDurationConversions(duration: java.time.Duration) {
    def toScala: FiniteDuration = FiniteDuration(duration.toMillis, TimeUnit.MILLISECONDS)
  }

  /**
    * Mockito breaks reflection when mocking classes, for example:
    *
    * interface A { }
    * class B extends A
    * val b = mock[B]
    *
    * When inspecting b, the fact that it extends from A can no longer be reflected.
    *
    * Here we obtain the original class that was mocked.
    *
    * @param clazz The (potentially mocked) class
    * @return The original class
    */
  def unmock(clazz: Class[_]) = {

    if (clazz.getName.contains("$$EnhancerByMockitoWithCGLIB$$")) {
      val originalName: String = clazz.getName.split("\\$\\$EnhancerByMockitoWithCGLIB\\$\\$")(0)
      clazz.getClassLoader.loadClass(originalName)
    } else
      clazz
  }

  def namedCachedThreadPool(threadNamePrefix: String): ExecutionContext =
    ExecutionContext.fromExecutorService(Executors.newCachedThreadPool(daemonThreadFactory(threadNamePrefix)))

  /** A `ThreadFactory` which creates daemon threads, using the given name. */
  def daemonThreadFactory(threadName: String, exitJvmOnFatalError: Boolean = true): ThreadFactory = new ThreadFactory {
    val defaultThreadFactory = Executors.defaultThreadFactory()
    val idx = new AtomicInteger(0)
    def newThread(r: Runnable) = {
      val t = defaultThreadFactory.newThread(r)
      t.setDaemon(true)
      t.setName(s"$threadName-${idx.incrementAndGet()}")
      t.setUncaughtExceptionHandler(new UncaughtExceptionHandler {
        def uncaughtException(t: Thread, e: Throwable): Unit = {
          System.err.println(s"------------ UNHANDLED EXCEPTION ---------- (${t.getName})")
          e.printStackTrace(System.err)
          if (exitJvmOnFatalError) {
            e match {
              case NonFatal(_) => ()
              case fatal => System.exit(-1)
            }
          }
        }
      })
      t
    }
  }
}
