package com.ing.baker.runtime.akka.internal

import java.util.{Timer, TimerTask}
import scala.concurrent.{ExecutionContext, Future, Promise, TimeoutException}
import scala.concurrent.duration.FiniteDuration

// Taken from https://stackoverflow.com/questions/16304471/scala-futures-built-in-timeout and updated.
private[baker] object TimeoutUtil {
  // All Future's that use futureWithTimeout will use the same Timer object
  // it is thread safe and scales to thousands of active timers
  // The true parameter ensures that timeout timers are daemon threads and do not stop
  // the program from shutting down

  val timer: Timer = new Timer(true)

  implicit class TimeoutExtension[T](future: Future[T]) {
    /**
      * Returns the result of the provided future within the given time or a timeout exception, whichever is first
      * This uses Java Timer which runs a single thread to handle all futureWithTimeouts and does not block like a
      * Thread.sleep would
      *
      * @param timeout Time before we return a Timeout exception instead of future's outcome
      * @return Future[T]
      */
    def withTimeout(timeout: FiniteDuration, message: String)(implicit ec: ExecutionContext): Future[T] = {

      // Promise will be fulfilled with either the callers Future or the timer task if it times out
      val p = Promise[T]()

      // and a Timer task to handle timing out

      val timerTask = new TimerTask() {
        def run(): Unit = {
          p.tryFailure(new TimeoutException(message))
        }
      }

      // Set the timeout to check in the future
      timer.schedule(timerTask, timeout.toMillis)

      future.map {
        a =>
          if (p.trySuccess(a)) {
            timerTask.cancel()
          }
      }
        .recover {
          case e: Exception =>
            if (p.tryFailure(e)) {
              timerTask.cancel()
            }
        }

      p.future
    }
  }


}
