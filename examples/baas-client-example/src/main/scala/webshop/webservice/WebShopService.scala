package webshop.webservice

import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import webshop.webservice.WebShopService.Implicits._
import webshop.webservice.WebShopService._

object WebShopService {

  case class PlaceOrderRequest(items: List[String])

  case class PlaceOrderResponse(orderId: String)

  case class AddAddressRequest(address: String)

  case class AddPaymentRequest(payment: String)

  case class PollPaymentStatusResponse(status: String)

  object Implicits {

    implicit val placeOrderRequestDecoder: EntityDecoder[IO, PlaceOrderRequest] =
      accumulatingJsonOf[IO, PlaceOrderRequest]
    implicit val placeOrderResponseDecoder: EntityDecoder[IO, PlaceOrderResponse] =
      accumulatingJsonOf[IO, PlaceOrderResponse]
    implicit val addAddressRequestDecoder: EntityDecoder[IO, AddAddressRequest] =
      accumulatingJsonOf[IO, AddAddressRequest]
    implicit val addPaymentRequestDecoder: EntityDecoder[IO, AddPaymentRequest] =
      accumulatingJsonOf[IO, AddPaymentRequest]
    implicit val pollPaymentStatusResponseDecoder: EntityDecoder[IO, PollPaymentStatusResponse] =
      accumulatingJsonOf[IO, PollPaymentStatusResponse]
  }
}

class WebShopService(webshop: WebShop)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

  def build: HttpApp[IO] =
    (root <+> api).orNotFound

  def root: HttpRoutes[IO] = Router("/" -> HttpRoutes.of[IO] {

    case GET -> Root => Ok("Ok")
  })

  def api: HttpRoutes[IO] = Router("/api" -> HttpRoutes.of[IO] {

    case GET -> Root =>
      Ok("Ok")

    case GET -> Root / "recipe-names" =>
      for {
        recipeNames <- webshop.listRecipeNames
        response <- Ok(recipeNames.mkString(","))
      } yield response

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

  })
}
