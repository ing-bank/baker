package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke.k8s.DefinitionFile
import com.ing.baker.baas.testing.BakeryFunSpec
import org.http4s.Uri
import org.scalatest.{ConfigMap, Matchers}
import webshop.webservice.OrderStatus

class BakerySmokeTests extends BakeryFunSpec with Matchers {

  describe("The Bakery cluster") {

    test("runs a happy path flow") { context =>
      for {
        recipes <- context.clientApp.listRecipeNames
        _ = recipes.length shouldBe 1
        _ = recipes should contain("Webshop")

        _ <- DefinitionFile("baker-webshop-update-recipes.yaml", context.namespace)
        _ <- eventually("Webshop baker added an extra recipe") {
          for {
            recipes <- context.clientApp.listRecipeNames
            _ = recipes.length shouldBe 2
            _ = recipes should contain("Webshop")
            _ = recipes should contain("ItemReservation")
          } yield ()
        }

        orderId <- context.clientApp.createCheckoutOrder(List("item1", "item2"))

        _ <- eventually(s"Order created: $orderId") {
          context.clientApp.pollOrderStatus(orderId)
            .map(status => status shouldBe OrderStatus.InfoPending(List("ShippingAddress", "PaymentInformation")).toString)
        }

        _ <- context.clientApp.addCheckoutAddressInfo(orderId, "address")
        _ <- printGreen(s"Address information added")

        _ <- eventually(s"Address processed") {
          context.clientApp.pollOrderStatus(orderId)
            .map(status => status shouldBe OrderStatus.InfoPending(List("PaymentInformation")).toString)
        }

        _ <- context.clientApp.addCheckoutPaymentInfo(orderId, "payment-info")
        _ <- printGreen(s"Payment information added")

        _ <- eventually(s"Payment received") {
          context.clientApp.pollOrderStatus(orderId)
            .map(status => status shouldBe OrderStatus.ProcessingPayment.toString)
        }

        _ <- eventually(s"Order completed") {
          context.clientApp.pollOrderStatus(orderId)
            .map(status => status shouldBe OrderStatus.Complete.toString)
        }

        recipeEvents <- context.recipeEventListener.events
        bakerEvents <- context.bakerEventListener.events
        _ = recipeEvents.foreach { event =>
          List(
            "ShippingConfirmed",
            "PaymentSuccessful",
            "PaymentInformationReceived",
            "OrderPlaced",
            "ItemsReserved",
            "ShippingAddressReceived"
          ) should contain(event)
        }
        _ = bakerEvents.foreach { event =>
          List(
            "InteractionCompleted",
            "InteractionStarted",
            "InteractionCompleted",
            "InteractionCompleted",
            "InteractionStarted",
            "EventReceived",
            "EventReceived",
            "EventReceived",
            "InteractionStarted",
            "RecipeInstanceCreated",
            "RecipeAdded"
          ) should contain(event)
        }
        _ <- printGreen(s"Event listeners successfully notified (Note: ordering of events not enforced)")
      } yield succeed
    }
  }

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = BakeryEnvironment.Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = BakeryEnvironment.Arguments

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] =
    BakeryEnvironment.resource(testArguments)

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = {
    val clientAppHostname = Uri.unsafeFromString(
      config.getOptional[String]("client-app").getOrElse("http://localhost:8080"))
    val eventListenerHostname = Uri.unsafeFromString(
      config.getOptional[String]("event-listener").getOrElse("http://localhost:8082"))
    val bakerEventListenerHostname = Uri.unsafeFromString(
      config.getOptional[String]("baker-event-listener").getOrElse("http://localhost:8083"))
    BakeryEnvironment.Arguments(
      clientAppHostname = clientAppHostname,
      eventListenerHostname = eventListenerHostname,
      bakerEventListenerHostname = bakerEventListenerHostname
    )
  }

}
