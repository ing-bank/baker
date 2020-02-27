package webshop.webservice

import cats.effect.IO

trait WebShop {

  def createCheckoutOrder(items: List[String]): IO[String]

  def addCheckoutAddressInfo(orderId: String, address: String): IO[Unit]

  def addCheckoutPaymentInfo(orderId: String, paymentInfo: String): IO[Unit]

  def pollOrderStatus(orderId: String): IO[OrderStatus]

  def gracefulShutdown: IO[Unit]
}

