package com.ing.baker

import java.util.UUID

import akka.actor.ActorPath
import akka.cluster.MultiNodeClusterSpec
import akka.remote.testconductor.RoleName
import akka.remote.testkit.{MultiNodeConfig, MultiNodeSpec}
import akka.stream.ActorMaterializer
import akka.testkit.ImplicitSender
import better.files.File
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl.Examples.webshop
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.ing.baker.types.{PrimitiveValue, RecordValue}
import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.mockito.MockitoSugar

import scala.concurrent.{Await, ExecutionContext}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global


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
    def apply(order: String): EventInstance = {
      EventInstance(webshop.valid.name, Map.empty)
    }
  }

  object ManufactureGoods {
    val name: String = webshop.manufactureGoods.name
    def apply(order: String): EventInstance = {
      EventInstance(webshop.goodsManufactured.name, Map(
        webshop.goods.name -> PrimitiveValue("Good1")
      ))
    }
  }

  object SendInvoice {
    val name: String = webshop.sendInvoice.name
    def apply(info: webshop.CustomerInfo): EventInstance = {
      EventInstance(webshop.invoiceWasSent.name, Map.empty)
    }
  }

  object ShipGoods {
    val name: String = webshop.shipGoods.name
    def apply(goods: String, info: webshop.CustomerInfo): EventInstance = {
      EventInstance(webshop.goodsShipped.name, Map(
        webshop.trackingId.name -> PrimitiveValue("TrackingId1")
      ))
    }
  }

  def placeOrderRuntimeEvent: EventInstance =
    EventInstance(webshop.orderPlaced.name, Map(
      webshop.order.name -> PrimitiveValue("Order1")
    ))

  def receivedDataRuntimeEvent: EventInstance =
    EventInstance(webshop.customerInfoReceived.name, Map(
      webshop.customerInfo.name -> RecordValue(Map(
        "name" -> PrimitiveValue("customer-name"),
        "address" -> PrimitiveValue("customer-address"),
        "email" -> PrimitiveValue("customer-email")
      ))
    ))

  def paymentMadeRuntimeEvent: EventInstance =
    EventInstance(webshop.paymentMade.name, Map.empty)

  def seedNodeConfig(path: ActorPath): Config =
    ConfigFactory.parseString(s"""baker.cluster.seed-nodes = ["$path"]""")

  def implementations: Seq[InteractionInstance] = Seq(
    ValidateOrder,
    ManufactureGoods,
    SendInvoice,
    ShipGoods
  ).map(InteractionInstance.unsafeFrom)
}

class HappyPath extends MultiNodeSpec(HappyPathConfig)
  with MultiNodeClusterSpec
  with ImplicitSender {

  import HappyPath._
  import HappyPathConfig._
  import system.dispatcher

  override def beforeAll(): Unit = {
    super.beforeAll()
    File("target/journal").createDirectoryIfNotExists().delete()
    File("target/snapshots").createDirectoryIfNotExists().delete()
  }

  override def afterAll(): Unit = {
    Await.result(system.terminate(), 10.seconds)
  }

  def runHappyFlow(baker: Baker, recipeId: String, recipeInstanceId: String): Unit = {

    Await.result(baker.bake(recipeId, recipeInstanceId), 10 seconds)

    val sensoryEventStatus1 = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, placeOrderRuntimeEvent)
    Await.result(sensoryEventStatus1.flatMap(_ => baker.getRecipeInstanceState(recipeInstanceId)), 10 seconds).eventNames

    val sensoryEventStatus2 = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, receivedDataRuntimeEvent)
    Await.result(sensoryEventStatus2.flatMap(_ => baker.getRecipeInstanceState(recipeInstanceId)), 10 seconds).eventNames

    val sensoryEventStatus3 = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMadeRuntimeEvent)
    val events3 = Await.result(sensoryEventStatus3.flatMap(_ => baker.getRecipeInstanceState(recipeInstanceId)), 10 seconds).eventNames

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

      val materializer = ActorMaterializer()
      val config = ConfigFactory.load().withFallback(seedNodeConfig(node(node1)))
      val baker = Baker.akka(config, system, materializer)
      baker.addInteractionInstances(HappyPath.implementations)
      val compiled = RecipeCompiler.compileRecipe(webshop.webShopRecipe)
      val recipeId = Await.result(baker.addRecipe(compiled), 10 seconds)

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
