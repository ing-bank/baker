package com.ing.baker.runtime.actor

import java.util.UUID

import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.cluster.sharding.ShardRegion.Passivate
import akka.testkit.{ImplicitSender, TestKit}
import com.ing.baker.petrinet.dsl.colored
import com.ing.baker.petrinet.dsl.colored.{ColoredPetriNet, Place, Transition}
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor.AkkaTestBase.MockShardActor
import com.ing.baker.runtime.actor.ProcessInstance.Settings
import com.ing.baker.runtime.actor.serialization.AkkaObjectSerializer
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import fs2.Strategy
import org.scalatest.{BeforeAndAfterAll, WordSpecLike}

object AkkaTestBase {

  case object GetChild
  class MockShardActor(childActorProps: Props, childActorName: String = UUID.randomUUID().toString) extends Actor {
    val childActor = context.actorOf(childActorProps, childActorName)

    def receive = {
      case GetChild       ⇒ sender() ! childActor
      case Passivate(msg) ⇒ childActor ! msg
      case msg @ _        ⇒ childActor forward msg
    }
  }
}

abstract class AkkaTestBase extends TestKit(ActorSystem("testSystem"))
    with WordSpecLike
    with ImplicitSender
    with BeforeAndAfterAll {

  def coloredProps[S, E](
    topology: ColoredPetriNet,
    runtime: PetriNetRuntime[Place, Transition, S, E],
    settings: Settings): Props =

    Props(new ProcessInstance[Place, Transition, S, E](
      "test",
      topology,
      settings,
      runtime,
      colored.placeIdentifier,
      colored.transitionIdentifier)
    )

  override def afterAll() = {
    super.afterAll()
    shutdown(system)
  }

  def expectMsgInAnyOrderPF[Out](pfs: PartialFunction[Any, Out]*): Unit = {
    if (pfs.nonEmpty) {
      val total = pfs.reduce((a, b) ⇒ a.orElse(b))
      expectMsgPF() {
        case msg @ _ if total.isDefinedAt(msg) ⇒
          val index = pfs.indexWhere(pf ⇒ pf.isDefinedAt(msg))
          val pfn = pfs(index)
          pfn(msg)
          expectMsgInAnyOrderPF[Out](pfs.take(index) ++ pfs.drop(index + 1): _*)
      }
    }
  }

  val instanceSettings = Settings(
    evaluationStrategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadPool"),
    idleTTL = None,
    serializer = new AkkaObjectSerializer(system, NoEncryption)
  )

  def createPetriNetActor(props: Props, name: String)(implicit system: ActorSystem): ActorRef = {
    val mockShardActorProps = Props(new MockShardActor(props, name))
    system.actorOf(mockShardActorProps)
  }

  def createPetriNetActor[S, E](petriNet: ColoredPetriNet, runtime: PetriNetRuntime[Place, Transition, S, E], processId: String = UUID.randomUUID().toString)(implicit system: ActorSystem): ActorRef = {

    createPetriNetActor(coloredProps(petriNet, runtime, instanceSettings), processId)
  }
}
