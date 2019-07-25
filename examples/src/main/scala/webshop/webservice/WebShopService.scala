package webshop.webservice

import cats.data.Kleisli
import cats.effect.{ContextShift, IO, Timer}
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router

object WebShopService {

  case class PlaceOrderRequest(items: List[String])
  case class PlaceOrderResponse(orderId: String)

  case class AddAddressRequest(address: String)
  case class AddPaymentRequest(payment: String)

  case class PollPaymentStatusResponse(status: String)
}

class WebShopService(webshop: WebShop)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  import WebShopService._

  implicit val placeOrderRequestDecoder: EntityDecoder[IO, PlaceOrderRequest] =
    jsonOf[IO, PlaceOrderRequest]
  implicit val addAddressRequestDecoder: EntityDecoder[IO, AddAddressRequest] =
    jsonOf[IO, AddAddressRequest]
  implicit val addPaymentRequestDecoder: EntityDecoder[IO, AddPaymentRequest] =
    jsonOf[IO, AddPaymentRequest]

  def buildHttpService: Kleisli[IO, Request[IO], Response[IO]] =
    Router("/api" -> HttpRoutes.of[IO] {

      case req@POST -> Root / "order" =>
        for {
          request <- req.as[PlaceOrderRequest]
          orderId <- webshop.createCheckoutOrder(request.items)
          response <- Ok(PlaceOrderResponse(orderId).asJson)
        } yield response

      case req@PUT -> Root / "order" / orderId / "address" =>
        for {
          request <- req.as[AddAddressRequest]
          _ <- webshop.addCheckoutAddressInfo(orderId, request.address)
          response <- Ok()
        } yield response

      case req@PUT -> Root / "order" / orderId / "payment" =>
        for {
          request <- req.as[AddPaymentRequest]
          _ <- webshop.addCheckoutPaymentInfo(orderId, request.payment)
          response <- Ok()
        } yield response

      case GET -> Root / "order" / orderId =>
        for {
          status <- webshop.pollOrderStatus(orderId)
          response <- Ok(PollPaymentStatusResponse(status.toString).asJson)
        } yield response

    }).orNotFound

}
