package com.ing.baker

import java.util.UUID

import akka.actor.ActorPath
import akka.remote.testconductor.RoleName
import akka.remote.testkit.MultiNodeConfig
import akka.testkit.ImplicitSender
import akka.cluster.MultiNodeClusterSpec
import akka.remote.testkit.MultiNodeSpec
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.core.{Baker, RuntimeEvent}
import com.typesafe.config.{Config, ConfigFactory}
import com.ing.baker.recipe.scaladsl.Examples.webshop
import com.ing.baker.types.{PrimitiveValue, RecordValue}
import org.scalatest.mockito.MockitoSugar
import better.files.File

import scala.concurrent.duration._


/** NOTES:
  * The lack of events when using a cluster baker provider is a bug specific to such mode, events can be seen from normal local provider.
  */

object InMemoryJournalConfig extends MultiNodeConfig {
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

class InMemoryJournalSpecMultiJvmNode1 extends InMemoryJournal
class InMemoryJournalSpecMultiJvmNode2 extends InMemoryJournal

object InMemoryJournal extends MockitoSugar {

  object ValidateOrder {
    val name: String = webshop.validateOrder.name
    def apply(order: String): RuntimeEvent = {
      println(Console.MAGENTA_B + order + " validated!" + Console.RESET)
      RuntimeEvent(webshop.valid.name, Seq.empty)
    }
  }

  object ManufactureGoods {
    val name: String = webshop.manufactureGoods.name
    def apply(order: String): RuntimeEvent =
      RuntimeEvent(webshop.goodsManufactured.name, Map(
        webshop.goods.name -> PrimitiveValue("Good1")
      ).toSeq)
  }

  object SendInvoice {
    val name: String = webshop.sendInvoice.name
    def apply(info: webshop.CustomerInfo): RuntimeEvent =
      RuntimeEvent(webshop.invoiceWasSent.name, Seq.empty)
  }

  object ShipGoods {
    val name: String = webshop.shipGoods.name
    def apply(goods: String, info: webshop.CustomerInfo): RuntimeEvent =
      RuntimeEvent(webshop.goodsShipped.name, Map(
        webshop.trackingId.name -> PrimitiveValue("TrackingId1")
      ).toSeq)
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

  val process1Id: String = "!id:process-one!"

  val implementations: Seq[AnyRef] = Seq(
    ValidateOrder,
    ManufactureGoods,
    SendInvoice,
    ShipGoods
  )
}

class InMemoryJournal extends MultiNodeSpec(InMemoryJournalConfig)
  with MultiNodeClusterSpec
  with ImplicitSender {

  import InMemoryJournalConfig._
  import InMemoryJournal._

  override def beforeAll(): Unit = {
    super.beforeAll()
    File("target/journal").createDirectoryIfNotExists().delete()
    File("target/snapshots").createDirectoryIfNotExists().delete()
  }

  "A InMemoryJournal" must {

    "retrieve state from a remote process actor using in-memory journals" in {

      val baker = Baker(seedNodeConfig(node(node1)))
      enterBarrier("startup")

      runOn(node1) {

        val compiled = RecipeCompiler.compileRecipe(webshop.webShopRecipe)
        baker.addImplementations(InMemoryJournal.implementations)

        enterBarrier("recipe-setup")

        enterBarrier("sensory-event-1")

        enterBarrier("sensory-event-2")
      }

      runOn(node2) {

        val compiled = RecipeCompiler.compileRecipe(webshop.webShopRecipe)
        baker.addImplementations(InMemoryJournal.implementations)

        val recipeId = baker.addRecipe(compiled)
        val processState = baker.bake(recipeId, process1Id)
        println(Console.YELLOW + "Process State: " + processState + Console.RESET)

        enterBarrier("recipe-setup")

        val sensoryEventStatus1 = baker.processEvent(process1Id, placeOrderRuntimeEvent)
        println(Console.YELLOW + "Sensory Event Status 1: " + sensoryEventStatus1 + Console.RESET)
        val events1 = baker.events(process1Id)
        println(Console.YELLOW + "Events 1: " + events1 + Console.RESET)

        enterBarrier("sensory-event-1")

        val sensoryEventStatus2 = baker.processEvent(process1Id, receivedDataRuntimeEvent)
        println(Console.YELLOW + "Sensory Event Status 2: " + sensoryEventStatus2 + Console.RESET)
        val events2 = baker.events(process1Id)
        println(Console.YELLOW + "Events 2: " + events2 + Console.RESET)

        enterBarrier("sensory-event-2")

        val sensoryEventStatus3 = baker.processEvent(process1Id, paymentMadeRuntimeEvent)
        println(Console.YELLOW + "Sensory Event Status 3: " + sensoryEventStatus3 + Console.RESET)
        val events3 = baker.events(process1Id)
        println(Console.YELLOW + "Events 3: " + events3 + Console.RESET)

      }

      enterBarrier("finished")
    }

  }
}
