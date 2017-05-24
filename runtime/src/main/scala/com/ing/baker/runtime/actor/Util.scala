package com.ing.baker.runtime.actor

import akka.actor.{ActorSystem, PoisonPill, Props}
import akka.cluster.Cluster
import akka.pattern.ask
import akka.persistence.PersistentActor
import akka.util.Timeout
import GracefulShutdownActor.Leave
import io.kagera.akka.actor.PetriNetInstance
import io.kagera.akka.actor.PetriNetInstance.Settings
import io.kagera.dsl.colored
import io.kagera.dsl.colored.{Place, Transition, _}
import io.kagera.execution.JobExecutor

import scala.concurrent.Await
import scala.concurrent.duration._

object Util {

  def coloredPetrinetProps[S](topology: ColoredPetriNet, settings: Settings): Props =
    Props(new PetriNetInstance[Place, Transition, S](
      topology,
      settings,
      colored.jobPicker,
      new JobExecutor[S, Place, Transition](topology, colored.taskProvider[S], t ⇒ t.exceptionStrategy)(settings.evaluationStrategy),
      t ⇒ t.updateState.asInstanceOf[(S ⇒ Any ⇒ S)],
      colored.placeIdentifier,
      colored.transitionIdentifier)
    )

  def createPersistenceWarmupActor()(implicit actorSystem: ActorSystem, timeout: FiniteDuration) = {
    val actorRef = actorSystem.actorOf(Props(new PersistentActor() {
      override val persistenceId = s"dummy-${java.util.UUID.randomUUID()}"
      override def receiveCommand = {
        case msg @ _ => sender() ! msg
      }
      override def receiveRecover = Map.empty
    }))

    Await.result(actorRef.ask("ping")(Timeout(timeout)), timeout)
    actorRef ! PoisonPill
  }

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
    val cluster =  Cluster.get(actorSystem)
    cluster.leave(cluster.selfAddress)
  }
}
