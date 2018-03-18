package com.ing.baker.runtime.actor

import java.util.UUID

import akka.actor.{ActorLogging, ActorSystem, PoisonPill, Props}
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.PersistentActor
import akka.util.Timeout
import com.ing.baker.il.petrinet
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor.GracefulShutdownActor.Leave
import com.ing.baker.runtime.actor.process_instance.ProcessInstance
import com.ing.baker.runtime.actor.process_instance.ProcessInstance.Settings
import com.ing.baker.runtime.core._

import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, Future}

object Util {

  def recipePetriNetProps(recipeName: String, petriNet: RecipePetriNet, petriNetRuntime: PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent], settings: Settings): Props =
    Props(new ProcessInstance[Place, Transition, ProcessState, RuntimeEvent](
      recipeName,
      petriNet,
      settings,
      petriNetRuntime,
      petrinet.placeIdentifier,
      petrinet.transitionIdentifier)
    )

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


  val sequenceTimeoutExtra = 2 seconds

  def collectFuturesWithin[T](futures: Seq[Future[T]], timeout: FiniteDuration, using: akka.actor.Scheduler)(implicit ec: ExecutionContext): Seq[T] = {

    val timeoutFutures: Seq[Future[Option[T]]] = futures.map { f =>
      val timeoutFuture = akka.pattern.after(timeout, using)(Future.successful(None))
      Future.firstCompletedOf(Seq(f.map(result => Some(result)), timeoutFuture))
    }

    val combined = Future.sequence(timeoutFutures).map(list => list.collect { case Some(result) => result } )

    // we know all futures will timeout after 'timeout', to be sure we wait some extra
    Await.result(combined, timeout + sequenceTimeoutExtra)
  }
}