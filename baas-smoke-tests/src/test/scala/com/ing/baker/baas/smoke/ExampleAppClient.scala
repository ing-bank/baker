package com.ing.baker.baas.smoke

import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s.Method._
import org.http4s.circe._
import org.http4s.client.Client
import org.http4s.client.dsl.io._
import org.http4s.{Status, Uri}
import webshop.webservice.WebShopService.Implicits._
import webshop.webservice.WebShopService._

class ExampleAppClient(client: Client[IO], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def ping: IO[Status] =
    client.statusFromUri(hostname / "api")

  def createCheckoutOrder(items: List[String]): IO[String] = {
    val request = POST(
      PlaceOrderRequest(items).asJson,
      hostname / "api" / "order")
    client.expect[PlaceOrderResponse](request).map(_.orderId)
  }

  def addCheckoutAddressInfo(orderId: String, address: String): IO[Unit] = {
    val request = PUT(
      AddAddressRequest(address).asJson,
      hostname / "api" / "order" / orderId / "address")
    client.status(request).void
  }

  def addCheckoutPaymentInfo(orderId: String, paymentInfo: String): IO[Unit] = {
    val request = PUT(
      AddPaymentRequest(paymentInfo).asJson,
      hostname / "api" / "order" / orderId / "payment")
    client.status(request).void
  }

  def pollOrderStatus(orderId: String): IO[String] = {
    client.expect[PollPaymentStatusResponse](hostname / "api" / "order" / orderId).map(_.status)
  }
}
