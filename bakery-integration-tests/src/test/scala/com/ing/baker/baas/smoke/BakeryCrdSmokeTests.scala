package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, Pod}
import com.ing.baker.baas.testing.BakeryFunSpec
import io.circe.parser._
import org.http4s.Uri
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers
import webshop.webservice.OrderStatus

class BakeryCrdSmokeTests extends BakerySmokeTests with Matchers {

  describe("The Bakery cluster with CRDs") {

    test("runs a happy path flow") { context =>
      for {
        recipes <- context.clientApp.listRecipeNames
        _ = recipes.length shouldBe 1
        _ = recipes should contain("Webshop")

        _ <- DefinitionFile("crd/baker-webshop-update-recipes.yaml", context.namespace)
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

        recipeEvents <- Pod.execOnNamed("kafka-event-sink",
          context.namespace, Some("kafkacat"))(s"kafkacat -b localhost:9092 -C -t recipe-events -o 0 -c ${ExpectedRecipeEvents.size}")

        _ = recipeEvents
          .map(parse)
          .map(_.toOption.get.asObject.get.apply("name").get.asString.get) shouldBe ExpectedRecipeEvents

        bakerEvents <- Pod.execOnNamed("kafka-event-sink",
          context.namespace, Some("kafkacat"))(s"kafkacat -b localhost:9092 -C -t baker-events -o 0 -c ${ExpectedBakerEvents.size}")

        _ = bakerEvents
          .map(parse)
          .map(_.toOption.get.asObject.get.keys.head) shouldBe ExpectedBakerEvents

        _ <- printGreen(s"Event streams contain all required events")
      } yield succeed
    }
  }

  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] =
    BakeryEnvironment.resource(testArguments, BakeryEnvironment.crdNamespace)

}
