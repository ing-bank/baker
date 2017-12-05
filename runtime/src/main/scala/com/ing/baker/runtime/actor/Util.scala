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
import com.ing.baker.runtime.actor.ProcessInstance.Settings
import com.ing.baker.runtime.core._

import scala.concurrent.Await
import scala.concurrent.duration._

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

  def persistEventsForActor(actorPersistenceId: String, serializableEvents: List[AnyRef])(implicit actorSystem: ActorSystem, timeout: Timeout) = {

    case class PersistAllEvents(events: List[AnyRef])
    case object PersistAllEventsDone

    val actor = actorSystem.actorOf(Props(new PersistentActor() {

      override val persistenceId = actorPersistenceId
      override def receiveRecover = Map.empty

      override def receiveCommand: Receive = {
        case PersistAllEvents(events) =>
          persistAll(events) { _ =>
            context.stop(self)
            sender() ! PersistAllEventsDone
          }
      }
    }))

    import akka.pattern.ask
    Await.result(actor.ask(PersistAllEvents(serializableEvents)), timeout.duration)
  }

  def handOverShardsAndLeaveCluster(typeNames: Seq[String])(implicit timeout: Timeout, actorSystem: ActorSystem): Unit = {

    // first hand over the shards
    val actor = actorSystem.actorOf(GracefulShutdownActor.props(timeout.duration, typeNames))
    Await.result(actor.ask(Leave), timeout.duration)

    // then leave the cluster
    val cluster = Cluster.get(actorSystem)
    cluster.leave(cluster.selfAddress)
  }

  class AwaitPersistenceInit extends PersistentActor with ActorLogging {
    override val persistenceId: String = s"persistenceInit-${UUID.randomUUID()}"
    log.info("Starting PersistenceInit actor with id: {}", persistenceId)

    def receiveRecover: Receive = {
      case _ => // intentionally left empty
    }

    def receiveCommand: Receive = {
      case msg =>
        log.info("Received message {}", msg)
        persist(msg) { _ =>
          log.info("Successfully persisted a simple event. Sending message {} back...", msg)
          sender() ! msg
        }
    }

  }

  // Executes the given function 'executeAfterInit' only after PersistenceInit actor initialises and returns response
  def awaitPersistenceInit(journalInitializeTimeout: FiniteDuration)
                          (executeAfterInit: => Unit)
                          (implicit system: ActorSystem): Unit = {
    val persistenceInitActor = system.actorOf(Props(classOf[AwaitPersistenceInit]), s"persistenceInit-${UUID.randomUUID().toString}")
    try {
      Await.result(persistenceInitActor.ask("ping")(Timeout(journalInitializeTimeout)).mapTo[String], journalInitializeTimeout)
      executeAfterInit
    } catch {
      case e: Exception => throw new BakerException("Cannot initialize the PersistenceInit actor", e)
    } finally {
      persistenceInitActor ! PoisonPill
    }

  }

}