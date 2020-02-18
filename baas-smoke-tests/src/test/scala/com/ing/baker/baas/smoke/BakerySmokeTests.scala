package com.ing.baker.baas.smoke

import org.scalatest.Matchers
import webshop.webservice.OrderStatus

class BakerySmokeTests extends BakeryFunSpec with Matchers {

  def notify(text: String): Unit =
    println(Console.GREEN + text + Console.RESET)

  describe("The Bakery cluster") {

    test("runs a happy path flow") { context =>
      for {
        orderId <- context.clientApp.createCheckoutOrder(List("item1", "item2"))
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => status shouldBe OrderStatus.InfoPending(List("ShippingAddress", "PaymentInformation")).toString))
        _ = notify(s"Order created: $orderId")
        _ <- context.clientApp.addCheckoutAddressInfo(orderId, "address")
        _ = notify(s"Address information added")
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => status shouldBe OrderStatus.InfoPending(List("PaymentInformation")).toString))
        _ = notify(s"Address processed")
        _ <- context.clientApp.addCheckoutPaymentInfo(orderId, "payment-info")
        _ = notify(s"Payment information added")
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => status shouldBe OrderStatus.ProcessingPayment.toString))
        _ = notify(s"Payment received")
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => status shouldBe OrderStatus.Complete.toString))
        _ = notify(s"Order completed")
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
        _ = notify(s"Event listeners successfully notified (Note: ordering of events not enforced)")
      } yield succeed
    }
  }
}
