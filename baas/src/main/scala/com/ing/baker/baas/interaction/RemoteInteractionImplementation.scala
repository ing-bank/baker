package com.ing.baker.baas.interaction

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.{HttpMessage, HttpRequest, HttpResponse, StatusCodes}
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.runtime.core.interations.InteractionImplementation
import com.ing.baker.types.Value

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

//This is the interactionImplementation as running in the BAAS cluster
//This communicates with a RemoteInteractionimplementatoinClient that execute the request.
case class RemoteInteractionImplementation(override val name: String,
                                           hostname: String,
                                           port: Int) extends InteractionImplementation {

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
    implicit val defaultActorSystem = ActorSystem()
    import defaultActorSystem.dispatcher
    implicit val materializer = ActorMaterializer()(defaultActorSystem)

    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = s"$hostname:$port/$name",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromString("")))

    val returnMessage: HttpMessage = Await.result(responseFuture, 30 seconds)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, headers, entity, _) =>
        entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
          println("Got response, body: " + body.utf8String)
        }
      case resp@HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
      //        fail("Request failed, response code: " + code)
    }
    RuntimeEvent.create("", Seq.empty)
  }
}
