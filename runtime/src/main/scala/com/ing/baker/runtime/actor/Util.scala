package com.ing.baker.runtime.actor

import java.util.UUID
import java.util.concurrent.LinkedBlockingQueue
import java.util.concurrent.atomic.AtomicInteger

import akka.actor.{ActorLogging, ActorSystem, PoisonPill, Props}
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.PersistentActor
import akka.util.Timeout
import com.ing.baker.runtime.actor.GracefulShutdownActor.Leave

import scala.collection.JavaConverters._
import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, Future, Promise}
import scala.util.{Failure, Success}

object Util {

  def handOverShardsAndLeaveCluster(typeNames: Seq[String])(implicit timeout: Timeout, actorSystem: ActorSystem): Unit = {

    // first hand over the shards
    val actor = actorSystem.actorOf(GracefulShutdownActor.props(timeout.duration, typeNames))
    Await.result(actor.ask(Leave), timeout.duration)

    // then leave the cluster
    val cluster = Cluster.get(actorSystem)
    cluster.leave(cluster.selfAddress)
  }

  case object Ping extends InternalBakerMessage
  case object Pong extends InternalBakerMessage

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

    val persistenceInitActor = system.actorOf(Props(classOf[AwaitPersistenceInit]), s"persistenceInit-${UUID.randomUUID().toString}")

    import system.dispatcher

    persistenceInitActor.ask(Ping)(Timeout(journalInitializeTimeout)).map(_ => ())
  }

  private val sequenceTimeoutExtra = 10 seconds

  /**
    * Returns a future that returns a default value after a specified timeout.

    */
  def futureWithTimeout[T](future: Future[T], timeout: FiniteDuration, default: T, scheduler: akka.actor.Scheduler)(implicit ec: ExecutionContext): Future[T] = {
    val timeoutFuture = akka.pattern.after(timeout, scheduler)(Future.successful(default))
    Future.firstCompletedOf(Seq(future, timeoutFuture))
  }

  def collectFuturesWithin[T, M[X] <: scala.TraversableOnce[X]](futures: M[Future[T]], timeout: FiniteDuration, scheduler: akka.actor.Scheduler)(implicit ec: ExecutionContext): Seq[T] = {

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
}