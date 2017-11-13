package com.ing.baker.baas.interaction

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.{HttpMessage, HttpRequest, HttpResponse, StatusCodes}
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.baas.interaction.http.{ExecuteInteractionHTTPRequest, ExecuteInteractionHTTPResponse}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.runtime.core.interations.InteractionImplementation
import com.ing.baker.types.Value
import org.slf4j.LoggerFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

//This is the interactionImplementation as running in the BAAS cluster
//This communicates with a RemoteInteractionimplementatoinClient that execute the request.
case class RemoteInteractionImplementation(override val name: String,
                                           hostname: String,
                                           port: Int)(implicit val actorSystem: ActorSystem) extends InteractionImplementation {

  val log = LoggerFactory.getLogger(classOf[RemoteInteractionImplementation])

  override def isValidForInteraction(interaction: InteractionTransition[_]): Boolean =
    interaction.originalInteractionName == name

  /**
    * Executes the interaction.
    *
    * TODO input could be map instead of sequence??
    *
    * @param input
    * @return
    */
  override def execute(interaction: InteractionTransition[_], input: Seq[Value]): RuntimeEvent = {
    //Call HTTP endpoint
//    implicit val defaultActorSystem = ActorSystem()
    implicit val materializer = ActorMaterializer()

    val uri = s"http://$hostname:$port/$name"
    log.info(s"Calling remote execution of interaction: $name on $uri")

    val request = ExecuteInteractionHTTPRequest(interaction, input)

    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = uri,
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(kryoPool.toBytesWithClass(request))))

    val returnMessage: HttpMessage = Await.result(responseFuture, 30 seconds)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, headers, entity, _) =>
        log.info(s"Ok response received for executing request")
        val body: ByteString = Await.result(entity.dataBytes.runFold(ByteString(""))(_ ++ _), 30 seconds)
        val response: ExecuteInteractionHTTPResponse = kryoPool.fromBytes(body.toArray).asInstanceOf[ExecuteInteractionHTTPResponse]
        log.info(s"Executing of interaction passed with runtime event $response")
        response.runtimeEvent
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Executing interaction failed with code: " + code)
        throw new RuntimeException("Executing interaction failed")
    }
  }
}
