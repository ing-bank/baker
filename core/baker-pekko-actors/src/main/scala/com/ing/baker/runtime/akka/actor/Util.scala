package com.ing.baker.runtime.akka.actor

import org.apache.pekko.actor.{ActorLogging, ActorSystem, NoSerializationVerificationNeeded, PoisonPill, Props, Scheduler}
import org.apache.pekko.event.DiagnosticLoggingAdapter
import org.apache.pekko.event.Logging.LogLevel
import org.apache.pekko.pattern
import org.apache.pekko.pattern.ask
import org.apache.pekko.persistence.PersistentActor
import org.apache.pekko.util.Timeout

import java.util.UUID
import java.util.concurrent.LinkedBlockingQueue
import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.nowarn
import scala.jdk.CollectionConverters._
import scala.concurrent._
import scala.concurrent.duration.{FiniteDuration, _}
import scala.util.{Failure, Success}

object Util {

  case object Ping extends NoSerializationVerificationNeeded

  case object Pong extends NoSerializationVerificationNeeded

  class AwaitPersistenceInit extends PersistentActor with ActorLogging {

    override val persistenceId: String = s"persistenceInit-${UUID.randomUUID()}"

    log.info("Starting PersistenceInit actor with id: {}", persistenceId)

    // intentionally left empty
    def receiveRecover: Receive = Map.empty

    // intentionally left empty
    def receiveCommand: Receive = {
      case Ping =>
        log.info("Received persistence init")
        sender() ! Pong
        context.self ! PoisonPill
    }
  }

  // Executes the given function 'executeAfterInit' only after PersistenceInit actor initialises and returns response
  def persistenceInit(journalInitializeTimeout: FiniteDuration)(implicit system: ActorSystem): Future[Unit] = {

    import system.dispatcher

    val persistenceInitActor = system.actorOf(Props(classOf[AwaitPersistenceInit]), s"persistenceInit-${UUID.randomUUID().toString}")

    persistenceInitActor.ask(Ping)(Timeout(journalInitializeTimeout)).map(_ => ())
  }

  private val sequenceTimeoutExtra = 10 seconds

  /**
    * Returns a future that returns a default value after a specified timeout.

    */
  def futureWithTimeout[T](future: Future[T], timeout: FiniteDuration, default: T, scheduler: Scheduler)(implicit ec: ExecutionContext): Future[T] = {
    val timeoutFuture = pattern.after(timeout, scheduler)(Future.successful(default))
    Future.firstCompletedOf(Seq(future, timeoutFuture))
  }

  @nowarn
  def collectFuturesWithin[T, M[X] <: scala.TraversableOnce[X]](futures: M[Future[T]], timeout: FiniteDuration, scheduler: Scheduler)(implicit ec: ExecutionContext): Seq[T] = {

    val size = futures.size
    val queue = new LinkedBlockingQueue[T](size)
    val counter = new AtomicInteger(0)
    val promise = Promise[List[T]]()

    def completePromise() = promise.trySuccess(queue.iterator().asScala.toList)

    futures.foreach { _.onComplete {
        case Success(result) =>
          queue.put(result)
          if (counter.incrementAndGet() == size)
            completePromise()
        case Failure(_) =>
          if (counter.incrementAndGet() == size)
            completePromise()
      }
    }

    scheduler.scheduleOnce(timeout) {
      completePromise()
    }

    Await.result(promise.future, timeout + sequenceTimeoutExtra)
  }

  object logging {

    implicit class DiagnosticLoggingAdapterFns(log: DiagnosticLoggingAdapter) {

      @nowarn
      def errorWithMDC(msg: String, mdc: Map[String, Any], cause: Throwable) = {
        try {
          log.setMDC(mdc.asJava)
          log.error(cause, msg)
        } finally {
          log.clearMDC()
        }
      }

      @nowarn
      def logWithMDC(level: LogLevel, msg: String, mdc: Map[String, Any]) = {
        try {
          log.setMDC(mdc.asJava)
          log.log(level, msg)
        } finally {
          log.clearMDC()
        }
      }
    }

  }
}