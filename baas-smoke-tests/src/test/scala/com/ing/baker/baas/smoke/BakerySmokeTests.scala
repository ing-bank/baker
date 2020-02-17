package com.ing.baker.baas.smoke

import webshop.webservice.OrderStatus

class BakerySmokeTests extends BakeryFunSpec {

  def notify(text: String): Unit =
    println(Console.GREEN + text + Console.RESET)

  describe("The Bakery cluster") {

    test("runs a happy path flow") { context =>
      for {
        orderId <- context.clientApp.createCheckoutOrder(List("item1", "item2"))
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => assert(status == OrderStatus.InfoPending(List("ShippingAddress", "PaymentInformation")).toString)))
        _ = notify(s"Order created: $orderId")
        _ <- context.clientApp.addCheckoutAddressInfo(orderId, "address")
        _ = notify(s"Address information added")
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => assert(status == OrderStatus.InfoPending(List("PaymentInformation")).toString)))
        _ = notify(s"Address processed")
        _ <- context.clientApp.addCheckoutPaymentInfo(orderId, "payment-info")
        _ = notify(s"Payment information added")
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => assert(status == OrderStatus.ProcessingPayment.toString)))
        _ = notify(s"Payment received")
        _ <- eventually(context.clientApp.pollOrderStatus(orderId)
          .map(status => assert(status == OrderStatus.Complete.toString)))
        _ = notify(s"Order completed")
      } yield succeed
    }
  }
}
