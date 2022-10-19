package com.ing.baker.http.client.common

import cats.effect.IO
import cats.implicits._
import com.ing.baker.http.client.scaladsl.{EndpointConfig, ResponseError}
import com.ing.baker.runtime.common.BakerException
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.scaladsl.BakerResult
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import io.circe.Decoder
import org.http4s.circe.jsonOf
import org.http4s.client.Client
import org.http4s.client.middleware.Logger
import org.http4s.{Request, Response, Uri}
import retry.RetryPolicies.{constantDelay, limitRetries}
import retry.{RetryDetails, retryingOnAllErrors}

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import cats.effect.Temporal

object FailoverUtils extends LazyLogging {

  case class Config(initialDelay: FiniteDuration, retryTimes: Int)

  def handleHttpErrors(errorResponse: Response[IO]): IO[Throwable] =
    errorResponse.bodyText.compile.foldMonoid.map(body =>
      ResponseError(errorResponse.status.code, body)
    )

  def handleFallbackAwareErrors(errorResponse: Response[IO]): IO[Throwable] =
    errorResponse.bodyText.compile.foldMonoid.map { body =>
      val responseCode = errorResponse.status.code

      if (responseCode == 404) {
        NoSuchProcessException("UNKNOWN")
      } else {
        ResponseError(responseCode, body)
      }
    }

  private val config: Config = loadConfig

  /**
    * retry the HttpCall on different hosts
    *
    * @param fos  Hosts storage with state (knows the last failed)
    * @param request Function that returns request from host
    * @param ec   ExecutionContext
    * @return
    */
  def callWithFailOver(fos: FailoverState,
                       client: Client[IO],
                       request: (Uri, String) => IO[Request[IO]],
                       filters: Seq[Request[IO] => Request[IO]],
                       handleHttpErrors: Response[IO] => IO[Throwable],
                       fallbackEndpoint: Option[EndpointConfig])
                      (implicit ec: ExecutionContext, decoder: Decoder[BakerResult]): IO[BakerResult] = {
    implicit val timer: Temporal[IO] = IO.timer(ec)
    implicit val cs: ContextShift[IO] = IO.contextShift(ec)

    retryingOnAllErrors(
      policy = limitRetries[IO](
        (fos.endpoint.hosts.size + fallbackEndpoint.map(_.hosts.size).getOrElse(0)) * config.retryTimes) |+| constantDelay[IO](config.initialDelay),
      onError = (ex: Throwable, retryDetails: RetryDetails) => IO {
        ex match {
          case _: BakerException.NoSuchProcessException if fallbackEndpoint.isDefined =>
            fallbackEndpoint.foreach( fep => {
              logger.info(s"Retrying to fallback Baker API: $fep")
              fos.fallback(fep)
            })
          case _ =>
            val message = s"Failed to call ${fos.uri}, retry #${retryDetails.retriesSoFar}, error: ${ex.getMessage}"
            fos.failed()
            if (retryDetails.givingUp) logger.error(message) else logger.debug(message)
        }
      })(
      Logger(logBody = fos.endpoint.apiLoggingEnabled,
        logHeaders = fos.endpoint.apiLoggingEnabled,
        logAction = Some((s: String) => IO(logger.debug(s))))(client)
        .expectOr[BakerResult](
          request(fos.uri, fos.endpoint.apiUrlPrefix)
            .map({ request: Request[IO] => filters.foldLeft(request)((acc, filter) => filter(acc))})
        )(handleHttpErrors)(jsonOf[IO, BakerResult])
    )
  }

  private[common] def loadConfig: Config = {
    val config = ConfigFactory.load().getConfig("baker.client.failover")
    Config(Duration.fromNanos(config.getDuration("initial-delay").toNanos), config.getInt("retry-times"))
  }
}
