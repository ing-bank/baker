package com.ing.baker.runtime.akka.actor

import akka.actor.ActorSystem
import akka.testkit.{ImplicitSender, TestKit}
import io.prometheus.client.CollectorRegistry
import org.scalactic.source.Position
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatest.wordspec.AnyWordSpecLike

abstract class AkkaTestBase(actorSystemName: String = "testActorSystem") extends TestKit(ActorSystem(actorSystemName))
    with AnyWordSpecLike
    with ImplicitSender
    with BeforeAndAfterAll {

  override def beforeAll() = {
    super.beforeAll()
    CollectorRegistry.defaultRegistry.clear()
  }

  override def afterAll() = {
    super.afterAll()
    shutdown(system)
    CollectorRegistry.defaultRegistry.clear()
  }

  def expectMsgInAnyOrderPF[Out](pfs: PartialFunction[Any, Out]*): Unit = {
    if (pfs.nonEmpty) {
      val total = pfs.reduce((a, b) => a.orElse(b))
      expectMsgPF() {
        case msg @ _ if total.isDefinedAt(msg) =>
          val index = pfs.indexWhere(pf => pf.isDefinedAt(msg))
          val pfn = pfs(index)
          pfn(msg)
          expectMsgInAnyOrderPF[Out](pfs.take(index) ++ pfs.drop(index + 1): _*)
      }
    }
  }
}
