package com.ing.baker.runtime.actor

import java.util.UUID

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.testkit.{ImplicitSender, TestKit}
import com.ing.baker.petrinet.dsl.colored
import com.ing.baker.petrinet.dsl.colored.{ColoredPetriNet, Place, Transition}
import com.ing.baker.petrinet.runtime._
import com.ing.baker.runtime.actor.process_instance.ProcessInstance
import com.ing.baker.runtime.actor.process_instance.ProcessInstance.Settings
import com.ing.baker.runtime.actor.serialization.Encryption.NoEncryption
import org.scalatest.{BeforeAndAfterAll, WordSpecLike}


abstract class AkkaTestBase(actorSystemName: String = "testActorSystem") extends TestKit(ActorSystem(actorSystemName))
    with WordSpecLike
    with ImplicitSender
    with BeforeAndAfterAll {

  val testExecutionContext = namedCachedThreadPool(s"Baker.CachedThreadPool")

  def coloredProps[S, E](
    topology: ColoredPetriNet,
    runtime: PetriNetRuntime[Place, Transition, S, E],
    settings: Settings): Props =

    Props(new ProcessInstance[Place, Transition, S, E](
      "test",
      topology,
      settings,
      runtime)
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
    executionContext = testExecutionContext,
    idleTTL = None,
    encryption = NoEncryption
  )

  def createPetriNetActor(props: Props, name: String)(implicit system: ActorSystem): ActorRef = {
    system.actorOf(props, name)
  }

  def createPetriNetActor[S, E](petriNet: ColoredPetriNet, runtime: PetriNetRuntime[Place, Transition, S, E], processId: String = UUID.randomUUID().toString)(implicit system: ActorSystem): ActorRef = {

    createPetriNetActor(coloredProps(petriNet, runtime, instanceSettings), processId)
  }
}
