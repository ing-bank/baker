package com.ing.bakery.common

import cats.effect.{IO, Timer}
import cats.implicits._
import com.ing.baker.runtime.scaladsl.BakerResult
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import io.circe.Decoder
import org.http4s.circe.jsonOf
import org.http4s.client.Client
import org.http4s.{Request, Response, Uri}
import retry.RetryPolicies.{exponentialBackoff, limitRetries}
import retry.{RetryDetails, retryingOnAllErrors}

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

object FailoverUtils extends LazyLogging {

  case class Config(initialDelay: FiniteDuration, retryTimes: Int)

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
                       request: Uri => IO[Request[IO]],
                       filters: Seq[Request[IO] => Request[IO]],
                       handleHttpErrors: Response[IO] => IO[Throwable])
                      (implicit ec: ExecutionContext, decoder: Decoder[BakerResult]): IO[BakerResult] = {
    implicit val timer: Timer[IO] = IO.timer(ec)

    def call(uri: Uri): IO[BakerResult] =
      client
        .expectOr(request(uri).map({ request: Request[IO] =>
          filters.foldLeft(request)((acc, filter) => filter(acc))
        }))(handleHttpErrors)(jsonOf[IO, BakerResult])

    retryingOnAllErrors(
      policy = limitRetries[IO](fos.size * config.retryTimes) |+| exponentialBackoff[IO](config.initialDelay),
      onError = (ex: Throwable, retryDetails: RetryDetails) => IO {
        val message = s"Failed to call ${fos.uri}, retry #${retryDetails.retriesSoFar}, error: ${ex.getMessage}"
        if (retryDetails.givingUp) logger.error(message) else logger.debug(message)
        fos.failed()
        ()
      })(call(fos.uri))
  }

  private[common] def loadConfig: Config = {
    val config = ConfigFactory.load().getConfig("baker.client.failover")

    Config(Duration.fromNanos(config.getDuration("initial-delay").toNanos), config.getInt("retry-times"))
  }
}
