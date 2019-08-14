package com.ing.baker.baas

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model._
import akka.stream.Materializer
import akka.util.ByteString
import com.ing.baker.baas.KryoUtil.defaultKryoPool
import org.slf4j.LoggerFactory

import scala.concurrent.Await
import scala.concurrent.duration.FiniteDuration

object ClientUtils {

  val log = LoggerFactory.getLogger(ClientUtils.getClass.getName)

  def entityFromResponse[T](entity: ResponseEntity)(implicit materializer: Materializer, timeout: FiniteDuration): T = {
    val byteString = Await.result(entity.dataBytes.runFold(ByteString(""))(_ ++ _), timeout)
    defaultKryoPool.fromBytes(byteString.toArray).asInstanceOf[T]
  }

  def doRequestAndParseResponse[T](httpRequest: HttpRequest)(implicit actorSystem: ActorSystem, materializer: Materializer, timeout: FiniteDuration): T = {

    doRequest(httpRequest, e => entityFromResponse[T](e))
  }

  def doRequest[T](httpRequest: HttpRequest, fn: ResponseEntity => T)(implicit actorSystem: ActorSystem, materializer: Materializer, timeout: FiniteDuration): T = {

    log.info(s"Sending request: $httpRequest")

    val response: HttpMessage = Await.result(Http().singleRequest(httpRequest), timeout)

    response match {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        fn(entity)
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Request failed with response code: " + code)
        throw new RuntimeException("Request failed with response code: " + code)
    }
  }
}
