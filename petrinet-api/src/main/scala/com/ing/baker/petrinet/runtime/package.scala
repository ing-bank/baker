package com.ing.baker.petrinet

import java.lang.Thread.UncaughtExceptionHandler
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.{Executors, ThreadFactory}

import cats.effect.IO
import com.ing.baker.petrinet.api.{Marking, MultiSet}

import scala.concurrent.ExecutionContext
import scala.util.control.NonFatal

package object runtime {

  /**
   * An exception handler function associated with a transition.
   */
  type TransitionExceptionHandler[P[_]] = (Throwable, Int, MultiSet[P[_]]) ⇒ ExceptionStrategy

  /**
   * An (asynchronous) function associated with a transition
   *
   * @tparam Input  The input delivered to the transition from outside the process.
   * @tparam Output The output emitted by the transition.
   * @tparam State  The state the transition closes over.
   */
  type TransitionTask[P[_], Input, E, State] = (Marking[P], State, Input) ⇒ IO[(Marking[P], E)]

  /**
   * An event sourcing function associated with a transition
   *
   * @tparam S The state type
   * @tparam E The event type
   */
  type EventSource[S, E] = S ⇒ E ⇒ S

  implicit class IOHandleErrors[T](io: IO[T]) {

    def handle[Y >: T](pf: PartialFunction[Throwable, Y]): IO[Y] =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).map(IO.pure(_)).getOrElse(IO.raiseError(throwable))
      }

    def handleWith[Y >: T](pf: PartialFunction[Throwable, IO[Y]]) =
      io.attempt.flatMap {
        case Right(result)   => IO.pure(result)
        case Left(throwable) => pf.lift(throwable).getOrElse(IO.raiseError(throwable))
      }
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
