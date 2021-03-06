package com.ing.bakery.smoke

import cats.effect.{IO, Resource}
import com.ing.bakery.smoke.k8s.{DefinitionFile, Pod}
import io.circe.parser._
import org.scalatest.matchers.should.Matchers
import webshop.webservice.OrderStatus
import scala.concurrent.duration._

class BakeryWebshopTests extends BakerySmokeTests  with Matchers {


  describe("The Bakery cluster") {

    test("runs a happy path flow") { context =>
      for {
        _ <- eventually {
          for {recipes <- context.clientApp.listRecipeNames
               _ = recipes.length shouldBe 1
               _ = recipes should contain("Webshop")
               } yield ()
        }
        _ <- DefinitionFile("extra-recipe.yaml", context.namespace)
        _ <- within(3 minutes, 30) {
          for {
            recipes <- context.clientApp.listRecipeNames
            _ = recipes.length shouldBe 2
            _ = recipes should contain("Webshop")
            _ = recipes should contain("ItemReservation.recipe")
            // 'ItemReservation.recipe' is the ID of this recipe
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

        events <- Pod.execOnNamed("kafka-event-sink",
          context.namespace, Some("kafkacat"))(s"kafkacat -b localhost:9092 -C -t events -o 0 -c ${ExpectedEvents.size}")
        _ = events
          .map(parse)
          .map(_.toOption.get.asObject.get.apply("name").get.asString.get).sorted shouldBe ExpectedEvents.sorted

        _ <- printGreen(s"Event streams contain all required events")
      } yield succeed
    }
  }

  val ExpectedEvents = List(
    "EventReceived",
    "EventReceived",
    "EventReceived",
    "InteractionCompleted",
    "InteractionCompleted",
    "InteractionCompleted",
    "InteractionStarted",
    "InteractionStarted",
    "InteractionStarted",
    "ItemsReserved",
    "OrderPlaced",
    "PaymentInformationReceived",
    "RecipeAdded",
    "RecipeAdded",
    "RecipeInstanceCreated",
    "ShippingAddressReceived",
    "ShippingConfirmed",
    "PaymentSuccessful"
  )


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
    BakeryEnvironment.resource(testArguments, BakeryEnvironment.namespace)

}
