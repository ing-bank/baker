package com.ing.baker

import java.util.UUID

import akka.actor.ActorPath
import akka.remote.testconductor.RoleName
import akka.remote.testkit.MultiNodeConfig
import akka.testkit.ImplicitSender
import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.MultiNodeSpec
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.akka.{AkkaBaker, RuntimeEvent}
import com.typesafe.config.{Config, ConfigFactory}
import com.ing.baker.recipe.scaladsl.Examples.webshop
import com.ing.baker.types.{PrimitiveValue, RecordValue}
import org.scalatest.mockito.MockitoSugar
import better.files.File
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.{Await, Future}
import scala.concurrent.duration._


/**
  * To run these tests: sbt integration/multi-jvm:test
  */
object HappyPathConfig extends MultiNodeConfig {
  val node1: RoleName = role("node1")
  val node2: RoleName = role("node2")
  val nodes: List[RoleName] = List(node1, node2)

  nodes.foreach { node =>
    nodeConfig(node)(ConfigFactory.parseString(s"""
      include "baker.conf"

      akka {
        actor {
          provider = cluster
          //provider = "akka.actor.LocalActorRefProvider"
          allow-java-serialization = off
        }
        persistence {
          journal.plugin = "akka.persistence.journal.leveldb"

          snapshot-store.plugin = "akka.persistence.snapshot-store.local"
          snapshot-store.local.dir = "target/snapshots/${node.name}"

          auto-start-snapshot-stores = ["akka.persistence.snapshot-store.local"]
          auto-start-journals = ["akka.persistence.journal.leveldb"]

          journal.leveldb.dir = "target/journal/${node.name}"
          journal.leveldb.native = off
        }

        loggers = ["akka.event.slf4j.Slf4jLogger"]
        loglevel = "DEBUG"
        logging-filter = "akka.event.slf4j.Slf4jLoggingFilter"
      }

      baker {
        actor.provider = "cluster-sharded"
        //actor.provider = "local"
        actor.read-journal-plugin = "akka.persistence.query.journal.leveldb"
        journal-initialize-timeout = 10 seconds
      }

      logging.root.level = DEBUG
      """))
  }

}

class HappyPathSpecMultiJvmNode1 extends HappyPath
class HappyPathSpecMultiJvmNode2 extends HappyPath

object HappyPath extends MockitoSugar {

  object ValidateOrder {
    val name: String = webshop.validateOrder.name
    def apply(order: String): RuntimeEvent = {
      RuntimeEvent(webshop.valid.name, Seq.empty)
    }
  }

  object ManufactureGoods {
    val name: String = webshop.manufactureGoods.name
    def apply(order: String): RuntimeEvent = {
      RuntimeEvent(webshop.goodsManufactured.name, Map(
        webshop.goods.name -> PrimitiveValue("Good1")
      ).toSeq)
    }
  }

  object SendInvoice {
    val name: String = webshop.sendInvoice.name
    def apply(info: webshop.CustomerInfo): RuntimeEvent = {
      RuntimeEvent(webshop.invoiceWasSent.name, Seq.empty)
    }
  }

  object ShipGoods {
    val name: String = webshop.shipGoods.name
    def apply(goods: String, info: webshop.CustomerInfo): RuntimeEvent = {
      RuntimeEvent(webshop.goodsShipped.name, Map(
        webshop.trackingId.name -> PrimitiveValue("TrackingId1")
      ).toSeq)
    }
  }

  def placeOrderRuntimeEvent: RuntimeEvent =
    RuntimeEvent(webshop.orderPlaced.name, Map(
      webshop.order.name -> PrimitiveValue("Order1")
    ).toSeq)

  def receivedDataRuntimeEvent: RuntimeEvent =
    RuntimeEvent(webshop.customerInfoReceived.name, Map(
      webshop.customerInfo.name -> RecordValue(Map(
        "name" -> PrimitiveValue("customer-name"),
        "address" -> PrimitiveValue("customer-address"),
        "email" -> PrimitiveValue("customer-email")
      ))
    ).toSeq)

  def paymentMadeRuntimeEvent: RuntimeEvent =
    RuntimeEvent(webshop.paymentMade.name, Seq.empty)

  def seedNodeConfig(path: ActorPath): Config =
    ConfigFactory.parseString(s"""baker.cluster.seed-nodes = ["$path"]""")

  val implementations: Seq[AnyRef] = Seq(
    ValidateOrder,
    ManufactureGoods,
    SendInvoice,
    ShipGoods
  )
}

class HappyPath extends MultiNodeSpec(HappyPathConfig)
  with MultiNodeClusterSpec
  with ImplicitSender {

  import HappyPathConfig._
  import HappyPath._

  override def beforeAll(): Unit = {
    super.beforeAll()
    File("target/journal").createDirectoryIfNotExists().delete()
    File("target/snapshots").createDirectoryIfNotExists().delete()
  }

  override def afterAll(): Unit = {
    Await.result(system.terminate(), 10.seconds)
  }

  def runHappyFlow(baker: Baker, recipeId: String, processId: String): Unit = {

    val processState = baker.bake(recipeId, processId)

    val sensoryEventStatus1 = baker.processEvent(processId, placeOrderRuntimeEvent)
    val events1 = baker.getProcessState(processId).eventNames

    val sensoryEventStatus2 = baker.processEvent(processId, receivedDataRuntimeEvent)
    val events2 = baker.getProcessState(processId).eventNames

    val sensoryEventStatus3 = baker.processEvent(processId, paymentMadeRuntimeEvent)
    val events3 = baker.getProcessState(processId).eventNames

    assert(events3 == List(
      webshop.orderPlaced.name,
      webshop.valid.name,
      webshop.customerInfoReceived.name,
      webshop.paymentMade.name,
      webshop.goodsManufactured.name,
      webshop.goodsShipped.name,
      webshop.invoiceWasSent.name)
    )
  }

  "A HappyPath" must {

    "retrieve state from a remote process actor using in-memory journals" in {

      val baker = new AkkaBaker(ConfigFactory.load().withFallback(seedNodeConfig(node(node1))))
      baker.addImplementations(HappyPath.implementations)
      val compiled = RecipeCompiler.compileRecipe(webshop.webShopRecipe)
      val recipeId = baker.addRecipe(compiled)

      enterBarrier("Setup finished")

      runOn(node1) {

        runHappyFlow(baker, recipeId, UUID.randomUUID().toString)
        runHappyFlow(baker, recipeId, UUID.randomUUID().toString)
        runHappyFlow(baker, recipeId, UUID.randomUUID().toString)

        enterBarrier("Happy flow finished")
      }

      runOn(node2) {

        runHappyFlow(baker, recipeId, UUID.randomUUID().toString)
        runHappyFlow(baker, recipeId, UUID.randomUUID().toString)
        runHappyFlow(baker, recipeId, UUID.randomUUID().toString)

        enterBarrier("Happy flow finished")
      }

      enterBarrier("finished")
    }

  }
}
