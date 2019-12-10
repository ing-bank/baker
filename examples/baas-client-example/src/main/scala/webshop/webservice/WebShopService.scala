package webshop.webservice

import java.io.File
import java.util.concurrent.Executors

import cats.data.Kleisli
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router

import scala.concurrent.ExecutionContext

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

  val blockingEc = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(4))

  def buildHttpService(shuttingDown: Ref[IO, Boolean]): Kleisli[IO, Request[IO], Response[IO]] =
    (Router("/" -> HttpRoutes.of[IO] {

      case GET -> Root => Ok("Ok")

      case HEAD -> Root =>
        shuttingDown.get.flatMap {
          case true => NotFound()
          case false => Ok()
        }

    }) <+>
      Router("/admin" -> HttpRoutes.of[IO] {

        case GET -> Root / "shutdown" =>
          for {
            _ <- shuttingDown.modify(_ => (true, ()))
            _ <- webshop.gracefulShutdown
            response <- Ok("down")
          } yield response
      }) <+>
      Router("/api" -> HttpRoutes.of[IO] {

        case GET -> Root =>
          Ok("Ok")

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

      })).orNotFound

  import java.lang.management.ManagementFactory

  import com.sun.management.HotSpotDiagnosticMXBean

  def dumpHeap(filePath: String, live: Boolean): IO[Unit] = IO {
    val file = new File(filePath)
    if (file.exists()) file.delete()
    val server = ManagementFactory.getPlatformMBeanServer
    val mxBean = ManagementFactory.newPlatformMXBeanProxy(server, "com.sun.management:type=HotSpotDiagnostic", classOf[HotSpotDiagnosticMXBean])
    mxBean.dumpHeap(filePath, live)
  }
}
