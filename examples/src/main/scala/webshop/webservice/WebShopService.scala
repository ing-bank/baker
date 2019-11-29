package webshop.webservice

import java.io.File
import java.util.concurrent.Executors

import cats.data.Kleisli
import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import io.circe.generic.auto._
import io.circe.syntax._
import org.http4s._
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import fs2.io.file
import java.util.UUID

import cats.effect.concurrent.{MVar, Ref}

import scala.concurrent.ExecutionContext

object WebShopService {

  case class PlaceOrderRequest(items: List[String])
  case class PlaceOrderResponse(orderId: String)

  case class AddAddressRequest(address: String)
  case class AddPaymentRequest(payment: String)

  case class PollPaymentStatusResponse(status: String)
}

class WebShopService(webshop: WebShop, memoryDumpPath: String)(implicit timer: Timer[IO], cs: ContextShift[IO]) {

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
        println(Console.GREEN + "SHUTTING DOWN" + Console.RESET)
        println(Console.GREEN + "====================" + Console.RESET)
        for {
          _ <- shuttingDown.modify(_ => (true, ()))
          _ <- webshop.gracefulShutdown
          response <- Ok("down")
        } yield response

      case GET -> Root / "memdump.hprof" =>
        val path = memoryDumpPath + "-" + UUID.randomUUID().toString + ".hprof"
        dumpHeap(path, live = true).as(
          Response[IO](
            Status.Ok,
            body = file.readAll[IO](java.nio.file.Paths.get(path), blockingEc, chunkSize = 4096),
            headers = Headers(headers.`Content-Type`(MediaType.application.`octet-stream`, Charset.`UTF-8`).pure[List]))
        )

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

  import com.sun.management.HotSpotDiagnosticMXBean
  import java.lang.management.ManagementFactory

  def dumpHeap(filePath: String, live: Boolean): IO[Unit] = IO {
    val file = new File(filePath)
    if (file.exists()) file.delete()
    val server = ManagementFactory.getPlatformMBeanServer
    val mxBean = ManagementFactory.newPlatformMXBeanProxy(server, "com.sun.management:type=HotSpotDiagnostic", classOf[HotSpotDiagnosticMXBean])
    mxBean.dumpHeap(filePath, live)
  }
}
